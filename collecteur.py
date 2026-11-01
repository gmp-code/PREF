#!/usr/bin/env python3
"""
Collecteur de veille des préfectures, exécuté par GitHub Actions (ou n'importe quelle machine).

Pour chaque préfecture :
  1. flux RSS Actualités (rss_feed_69), Publications (rss_feed_66) et tout flux de /syndication/listexport
     dont le titre évoque les arrêtés, le recueil, la presse ou l'ordre public ;
  2. page du recueil des actes administratifs : nouveaux PDF publiés (lecture directe, sans attendre data.gouv) ;
  3. préfecture de police de Paris : actualités et arrêtés.
Les PDF nouveaux sont téléchargés, convertis en texte (pdftotext) et filtrés sur les expressions de l'objet.
Résultat : data/veille.json, data/veille-public.json et data/arretes.json (lignes "auto") envoyés sur le site par FTP.
L'état (déjà vus) est conservé dans data/veille.json sur le site lui-même : aucun stockage côté GitHub.
"""
import concurrent.futures as cf, datetime as dt, hashlib, html, io, json, os, re, subprocess, sys, tempfile, time, urllib.parse, urllib.request, xml.etree.ElementTree as ET
from ftplib import FTP, FTP_TLS, error_perm

SITE = os.environ.get("SITE_URL", "https://front-administratif.fr").rstrip("/")
FTP_HOST, FTP_USER, FTP_PASS = os.environ.get("FTP_HOST", ""), os.environ.get("FTP_USER", ""), os.environ.get("FTP_PASS", "")
FTP_DIR = os.environ.get("FTP_DIR", "/public_html").rstrip("/")
NTFY = os.environ.get("NTFY_TOPIC", "")
NOTIF_CLE = os.environ.get("NOTIF_CLE", "")          # jeton VEILLE_CRON_CLE du site : permet l'alerte courriel via admin/notifier.php
RAA_API = "https://tabular-api.data.gouv.fr/api/resources/83c960be-1bb6-4b74-bbba-dcd6dcc3fbdf/data/"
RAA_PAGES = int(os.environ.get("RAA_PAGES", "30"))
AUTO_REGISTRE = os.environ.get("AUTO_REGISTRE", "1") == "1"
AUTO_PUBLIER = os.environ.get("AUTO_PUBLIER", "0") == "1"   # 1 = publier sans relecture ; 0 = déposer dans le tableau de bord, publication manuelle
UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36"
MAX_PDF = int(os.environ.get("MAX_PDF", "150"))
DIAG = os.environ.get("DIAG", "1") == "1"   # diagnostic du découpage dans le journal (mettre 0 pour alléger)
MAX_AGE_DAYS = 45
NOW = dt.datetime.now(dt.timezone.utc)
try:
    from zoneinfo import ZoneInfo; PARIS = NOW.astimezone(ZoneInfo("Europe/Paris"))
except Exception: PARIS = NOW

FORTS = re.compile(r"interdiction de manifest|interdisant .{0,80}manifest|manifestation.{0,60}interdi|interdiction .{0,40}rassemblement|rassemblement.{0,60}interdi|interdiction .{0,40}cort[eè]ge|attroupement|couvre[- ]feu|p[ée]rim[eè]tre .{0,30}(interdiction|s[ée]curit[ée]|protection)|captation.{0,60}(images|a[ée]ronef|drone)|cam[ée]ras? .{0,30}a[ée]ronefs?|dissimulation du visage|mineurs non accompagn|interdiction .{0,60}circul|libert[ée] de manifest|aller et venir|d[ée]claration de manifestation", re.I | re.S)
BANALS = re.compile(r"manifestation sportive|course cycliste|rallye|trail|marathon|chasse|p[êe]che en|brûlage|feux? de for[êe]t|s[ée]cheresse|grippe aviaire|enqu[êe]te publique|ICPE|[ée]olien", re.I)
# Communes : filtre durci. Expression du coeur de l'objet obligatoire ; vocabulaire de gestion exclu d'office.
COMMUNE_FORTS = re.compile(r"interdi\w+ .{0,80}(manifest|rassemblement|cort[eè]ge|attroupement)|(manifest|rassemblement|cort[eè]ge|attroupement)\w* .{0,60}interdi|attroupement|couvre[- ]feu|p[ée]rim[eè]tre (de )?(s[ée]curit[ée]|protection)|captation.{0,60}(images|a[ée]ronef|drone)|drone|vid[ée]oprotection|dissimulation du visage|mineurs? non accompagn|(station(nement)? assise|position allong[ée]e|mendicit[ée]|regroupement)|distribution (gratuite )?(de nourriture|alimentaire)|consommation d.alcool sur la voie publique", re.I | re.S)
COMMUNE_CIRCULATION = re.compile(r"interdiction .{0,60}circul", re.I)
COMMUNE_ORDRE = re.compile(r"ordre public|manifest|rassemblement|cort[eè]ge|attroupement|s[ée]curit[ée] des personnes", re.I)
COMMUNE_GESTION = re.compile(r"travaux|chantier|stationnement|d[ée]m[ée]nagement|[ée]lagage|nettoyage|nettoiement|fermeture (de la |du |de l.)?(piscine|gymnase|parc|jardin|cimeti[eè]re|stade|biblioth[eè]que|march[ée])|march[ée] (hebdomadaire|forain)|terrasse|occupation du domaine public|d[ée]bit de boissons|licence (ii|iii|iv)|feu d.artifice|course|f[êe]te (foraine|de quartier|votive)|c[ée]r[ée]monie|braderie|brocante|vide[- ]greniers?|tournage|grue|[ée]chafaudage|benne|livraison|emm[ée]nagement|d[ée]ratisation|p[ée]ril|insalubrit[ée]|num[ée]rotage|alignement|permis de (construire|d[ée]molir|am[ée]nager)|d[ée]l[ée]gation de (signature|fonction)|r[ée]gie|nomination|d[ée]signation|tarif", re.I)

def pertinent_commune(txt):
    """Un arrêté municipal n'est retenu que s'il porte le coeur de l'objet et aucun vocabulaire d'acte de gestion."""
    t = txt[:6000]
    if re.search(r"manifestation (sportive|culturelle|commerciale|a[ée]rienne|nautique)|course (cycliste|p[ée]destre)|rallye|marathon|trail", t, re.I): return False
    if COMMUNE_FORTS.search(t): return True           # coeur de l'objet : retenu même si l'acte parle aussi de stationnement
    if COMMUNE_GESTION.search(t): return False        # pour le reste, le vocabulaire de gestion écarte
    return bool(COMMUNE_CIRCULATION.search(t) and COMMUNE_ORDRE.search(t))

MOTS_RSS = ["manifestation", "manifester", "rassemblement", "cortège", "attroupement", "interdiction", "interdit", "périmètre", "couvre-feu", "drone", "aéronef", "captation", "caméra", "surveillance", "ordre public", "circulation", "liberté", "dissimulation du visage", "mineurs non accompagnés"]

def log(*a): print(*a, flush=True)

ERREURS = {}   # hôte -> dernière erreur HTTP/réseau (diagnostic)
def get(url, timeout=25, binary=False):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "fr-FR,fr;q=0.9", "Accept": "*/*"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = r.read(25 * 1024 * 1024)
            return data if binary else data.decode(r.headers.get_content_charset() or "utf-8", "replace")
    except urllib.error.HTTPError as e:
        ERREURS[urllib.parse.urlsplit(url).netloc] = f"HTTP {e.code}"; return None
    except Exception as e:
        ERREURS[urllib.parse.urlsplit(url).netloc] = type(e).__name__ + (": " + str(e)[:60] if str(e) else ""); return None

def propre(url):
    p = urllib.parse.urlsplit(url)
    path = "/".join(urllib.parse.quote(urllib.parse.unquote(s), safe="") for s in p.path.split("/"))
    return urllib.parse.urlunsplit((p.scheme or "https", p.netloc, path, p.query, ""))

def date_titre(t):
    mois = {"janvier":1,"fevrier":2,"février":2,"mars":3,"avril":4,"mai":5,"juin":6,"juillet":7,"aout":8,"août":8,"septembre":9,"octobre":10,"novembre":11,"decembre":12,"décembre":12}
    t = t.lower()
    m = re.search(r"\b(\d{1,2})(?:er)?\s+(janvier|f[ée]vrier|mars|avril|mai|juin|juillet|ao[uû]t|septembre|octobre|novembre|d[ée]cembre)\s+(\d{4})\b", t)
    if m: return "%04d-%02d-%02d" % (int(m.group(3)), mois.get(m.group(2), 1), int(m.group(1)))
    m = re.search(r"\b(\d{2})[-_/.](\d{2})[-_/.](\d{4})\b", t)
    if m and int(m.group(2)) <= 12: return f"{m.group(3)}-{m.group(2)}-{m.group(1)}"
    m = re.search(r"(?<!\d)(\d{4})[-_](\d{2})[-_](\d{2})(?!\d)", t)
    if m and int(m.group(2)) <= 12 and int(m.group(3)) <= 31: return f"{m.group(1)}-{m.group(2)}-{m.group(3)}"
    m = re.search(r"\b\d{2,3}-(\d{4})-(\d{2})-(\d{2})-\d{3,5}\b", t)   # numérotation des actes au RAA : 30-2026-10-29-00003
    if m and int(m.group(2)) <= 12 and int(m.group(3)) <= 31: return f"{m.group(1)}-{m.group(2)}-{m.group(3)}"
    return ""

def objet_propre(titre):
    """Titre d'acte lisible : majuscule initiale, espaces normalisés, sans mention de pagination."""
    t = re.sub(r"\s+", " ", (titre or "")).strip(" .;:-")
    t = re.sub(r"\s*\(\d+ pages?\)\s*", " ", t).strip()
    t = re.sub(r"\bPage \d+ :.*$", "", t).strip()
    if re.match(r"(portant|relatif|relative|instituant|interdisant|autorisant|r[ée]glementant|prescrivant|fixant|modifiant|instaurant|ordonnant)\b", t, re.I): t = "Arrêté " + t[:1].lower() + t[1:]
    return (t[:1].upper() + t[1:]) if t else "Acte sans titre"

DEPARTEMENTS = {"01":("Ain","de l'Ain"),"02":("Aisne","de l'Aisne"),"03":("Allier","de l'Allier"),"04":("Alpes-de-Haute-Provence","des Alpes-de-Haute-Provence"),"05":("Hautes-Alpes","des Hautes-Alpes"),"06":("Alpes-Maritimes","des Alpes-Maritimes"),"07":("Ardèche","de l'Ardèche"),"08":("Ardennes","des Ardennes"),"09":("Ariège","de l'Ariège"),"10":("Aube","de l'Aube"),"11":("Aude","de l'Aude"),"12":("Aveyron","de l'Aveyron"),"13":("Bouches-du-Rhône","des Bouches-du-Rhône"),"14":("Calvados","du Calvados"),"15":("Cantal","du Cantal"),"16":("Charente","de la Charente"),"17":("Charente-Maritime","de la Charente-Maritime"),"18":("Cher","du Cher"),"19":("Corrèze","de la Corrèze"),"2A":("Corse-du-Sud","de la Corse-du-Sud"),"2B":("Haute-Corse","de la Haute-Corse"),"21":("Côte-d'Or","de la Côte-d'Or"),"22":("Côtes-d'Armor","des Côtes-d'Armor"),"23":("Creuse","de la Creuse"),"24":("Dordogne","de la Dordogne"),"25":("Doubs","du Doubs"),"26":("Drôme","de la Drôme"),"27":("Eure","de l'Eure"),"28":("Eure-et-Loir","d'Eure-et-Loir"),"29":("Finistère","du Finistère"),"30":("Gard","du Gard"),"31":("Haute-Garonne","de la Haute-Garonne"),"32":("Gers","du Gers"),"33":("Gironde","de la Gironde"),"34":("Hérault","de l'Hérault"),"35":("Ille-et-Vilaine","d'Ille-et-Vilaine"),"36":("Indre","de l'Indre"),"37":("Indre-et-Loire","d'Indre-et-Loire"),"38":("Isère","de l'Isère"),"39":("Jura","du Jura"),"40":("Landes","des Landes"),"41":("Loir-et-Cher","de Loir-et-Cher"),"42":("Loire","de la Loire"),"43":("Haute-Loire","de la Haute-Loire"),"44":("Loire-Atlantique","de la Loire-Atlantique"),"45":("Loiret","du Loiret"),"46":("Lot","du Lot"),"47":("Lot-et-Garonne","de Lot-et-Garonne"),"48":("Lozère","de la Lozère"),"49":("Maine-et-Loire","de Maine-et-Loire"),"50":("Manche","de la Manche"),"51":("Marne","de la Marne"),"52":("Haute-Marne","de la Haute-Marne"),"53":("Mayenne","de la Mayenne"),"54":("Meurthe-et-Moselle","de Meurthe-et-Moselle"),"55":("Meuse","de la Meuse"),"56":("Morbihan","du Morbihan"),"57":("Moselle","de la Moselle"),"58":("Nièvre","de la Nièvre"),"59":("Nord","du Nord"),"60":("Oise","de l'Oise"),"61":("Orne","de l'Orne"),"62":("Pas-de-Calais","du Pas-de-Calais"),"63":("Puy-de-Dôme","du Puy-de-Dôme"),"64":("Pyrénées-Atlantiques","des Pyrénées-Atlantiques"),"65":("Hautes-Pyrénées","des Hautes-Pyrénées"),"66":("Pyrénées-Orientales","des Pyrénées-Orientales"),"67":("Bas-Rhin","du Bas-Rhin"),"68":("Haut-Rhin","du Haut-Rhin"),"69":("Rhône","du Rhône"),"70":("Haute-Saône","de la Haute-Saône"),"71":("Saône-et-Loire","de Saône-et-Loire"),"72":("Sarthe","de la Sarthe"),"73":("Savoie","de la Savoie"),"74":("Haute-Savoie","de la Haute-Savoie"),"75":("Paris","de police"),"76":("Seine-Maritime","de la Seine-Maritime"),"77":("Seine-et-Marne","de Seine-et-Marne"),"78":("Yvelines","des Yvelines"),"79":("Deux-Sèvres","des Deux-Sèvres"),"80":("Somme","de la Somme"),"81":("Tarn","du Tarn"),"82":("Tarn-et-Garonne","de Tarn-et-Garonne"),"83":("Var","du Var"),"84":("Vaucluse","de Vaucluse"),"85":("Vendée","de la Vendée"),"86":("Vienne","de la Vienne"),"87":("Haute-Vienne","de la Haute-Vienne"),"88":("Vosges","des Vosges"),"89":("Yonne","de l'Yonne"),"90":("Territoire de Belfort","du Territoire de Belfort"),"91":("Essonne","de l'Essonne"),"92":("Hauts-de-Seine","des Hauts-de-Seine"),"93":("Seine-Saint-Denis","de la Seine-Saint-Denis"),"94":("Val-de-Marne","du Val-de-Marne"),"95":("Val-d'Oise","du Val-d'Oise"),"971":("Guadeloupe","de la Guadeloupe"),"972":("Martinique","de la Martinique"),"973":("Guyane","de la Guyane"),"974":("La Réunion","de La Réunion"),"976":("Mayotte","de Mayotte")}

def pertinent_rss(txt):
    t = txt.lower()
    if re.search(r"\b(" + "|".join(["manifestation sportive", "course cycliste", "rallye", "trail", "marathon", "chasse", "pêche", "brûlage", "sécheresse", "grippe aviaire", "enquête publique"]) + r")\b", t): return False
    score = sum(1 for k in MOTS_RSS if k in t)
    fort = re.search(r"manifest|rassemblement|cort[eè]ge|attroupement|couvre[- ]feu|drone|a[ée]ronef|captation|p[ée]rim[eè]tre|dissimulation|mineurs non accompagn", t)
    return bool(fort) and score >= 2

def extraits(txt, n=3):
    out = []
    for m in FORTS.finditer(txt):
        a, b = max(0, m.start() - 90), min(len(txt), m.end() + 140)
        e = re.sub(r"\s+", " ", txt[a:b]).strip()
        if e not in out: out.append(e)
        if len(out) >= n: break
    return out

MOIS = {"janvier":1,"fevrier":2,"février":2,"mars":3,"avril":4,"mai":5,"juin":6,"juillet":7,"aout":8,"août":8,"septembre":9,"setptembre":9,"octobre":10,"novembre":11,"decembre":12,"décembre":12}
DATE_RX = re.compile(r"\b(\d{1,2})(?:er)?\s+(janvier|f[ée]vrier|mars|avril|mai|juin|juillet|ao[uû]t|se[pt]\w*embre|octobre|novembre|d[ée]cembre)\s+(\d{4})\b|\b(\d{2})/(\d{2})/(\d{4})\b", re.I)

def dates_dans(txt):
    out = []
    for m in DATE_RX.finditer(txt):
        try:
            if m.group(1):
                mo = MOIS.get(m.group(2).lower()) or (9 if m.group(2).lower().startswith("se") else None)
                if mo: out.append(dt.date(int(m.group(3)), mo, int(m.group(1))))
            else:
                out.append(dt.date(int(m.group(6)), int(m.group(5)), int(m.group(4))))
        except ValueError:
            pass
    return out

def fiche_acte(b, sig, ds, fin):
    """Fiche de lecture d'un arrêté : ce qu'il fait, ce qui est fragile, verdict. Lecture mécanique, à vérifier sur le texte."""
    t = b.lower()
    f = {"mesure": "", "territoire": "", "periode": "", "base_legale": "", "motivation": "", "points": [], "score": "faible", "verdict": ""}
    # Ce que l'acte fait
    mesures = []
    if re.search(r"interdi\w+ .{0,60}(manifest|rassemblement|cort[eè]ge|attroupement)|(manifest|rassemblement|cort[eè]ge|attroupement)\w* .{0,60}interdi", t): mesures.append("interdiction de manifester / de se rassembler")
    if re.search(r"couvre[- ]feu", t): mesures.append("couvre-feu" + (" des mineurs" if re.search(r"mineurs? non accompagn", t) else ""))
    if re.search(r"drone|a[ée]ronef|captation", t): mesures.append("captation d'images par aéronef")
    if re.search(r"dissimulation du visage|dissimuler .{0,20}visage", t): mesures.append("interdiction de dissimulation du visage")
    if re.search(r"p[ée]rim[eè]tre .{0,30}(s[ée]curit[ée]|protection)", t): mesures.append("périmètre de sécurité ou de protection")
    if re.search(r"interdiction .{0,60}circul", t): mesures.append("restriction de circulation")
    if re.search(r"artifices? de divertissement|carburant|armes? par destination|objets? pouvant constituer une arme", t): mesures.append("interdictions accessoires (artifices, carburants, armes par destination)")
    f["mesure"] = ", ".join(mesures) or "restriction d'une liberté (nature à préciser)"
    generale = bool(re.search(r"(tout|toute|tous|toutes)\s+(rassemblement|manifestation|cort[eè]ge|attroupement)", t)) and not re.search(r"d[ée]clar[ée]e? (par|le|la)|organis[ée]e? par|à l.appel de", t)
    if re.search(r"ensemble (du|de la) (territoire|commune|ville)|sur (tout|l.ensemble du) territoire", t): f["territoire"] = "commune entière"
    elif re.search(r"centre[- ]ville|hyper[- ]?centre", t): f["territoire"] = "centre-ville" + ("" if re.search(r"annexe|plan|carte|rues? (suivantes?|ci-apr[eè]s)|d[ée]limit", t) else " (périmètre non délimité dans le texte)")
    elif re.search(r"p[ée]rim[eè]tre", t): f["territoire"] = "périmètre défini" + ("" if re.search(r"annexe|plan|carte|d[ée]limit", t) else " (délimitation non lisible)")
    else: f["territoire"] = "non précisé"
    if sig and fin:
        j = (fin - sig).days
        f["periode"] = "du %s au %s (%d jour%s)" % (sig.strftime("%d/%m/%Y"), fin.strftime("%d/%m/%Y"), j, "s" if j > 1 else "")
    elif re.search(r"jusqu.à nouvel ordre|sans limitation de dur[ée]e|durée ind[ée]termin[ée]e", t): f["periode"] = "sans terme fixé"
    else: f["periode"] = "non reconnue dans le texte"
    bl = []
    for rx, lib in ((r"l\.\s*211-?\d*", "CSI, police des manifestations (L. 211)"), (r"l\.\s*2212|l\.\s*2214|l\.\s*2215", "CGCT, pouvoirs de police du maire / du préfet"), (r"l\.\s*242", "CSI, caméras aéroportées (L. 242)"), (r"code de la s[ée]curit[ée] int[ée]rieure", "code de la sécurité intérieure"), (r"code g[ée]n[ée]ral des collectivit[ée]s", "CGCT")):
        if re.search(rx, t): bl.append(lib)
    f["base_legale"] = ", ".join(dict.fromkeys(bl)) or "aucune base légale identifiable dans le texte"
    nb = len(re.findall(r"\bconsid[ée]rant\b", t))
    mc = re.search(r"\bconsid[ée]rant\b.*?(?=\n\s*(arr[êe]te|article 1|art\. 1)|$)", t, re.S)
    zone = mc.group(0) if mc else ""
    circ = bool(re.search(r"renseignement|signal[ée]|appels? (à la|sur les r[ée]seaux)|pr[ée]c[ée]dent[s]? (violence|d[ée]gradation)|d[ée]gradations? (constat|commis)|(le|les|du) \d{1,2} (septembre|octobre|novembre|d[ée]cembre|janvier|f[ée]vrier|mars|avril|mai|juin|juillet|ao[uû]t) \d{4}.{0,80}(violence|d[ée]gradation|incident|heurt|affrontement)", zone))
    f["motivation"] = ("%d considérant%s" % (nb, "s" if nb > 1 else "")) + (", avec des faits circonstanciés" if circ else ", sans fait précis ni daté cité") if nb else "aucun considérant"
    # Ce qui est fragile : constat -> pourquoi ça compte -> à vérifier
    P = f["points"]
    def pt(titre, pourquoi, verifier, poids): P.append({"titre": titre, "pourquoi": pourquoi, "verifier": verifier, "poids": poids})
    if generale: pt("Interdiction générale, sans manifestation visée", "Le juge exige qu'une interdiction soit nécessaire, adaptée et proportionnée au risque, pas une interdiction de principe (CE, 19 mai 1933, Benjamin).", "Existe-t-il une déclaration de manifestation ? L'arrêté cite-t-il un événement précis ?", 3)
    if f["territoire"].startswith("commune entière"): pt("Champ territorial : toute la commune", "Un risque localisé ne justifie pas une interdiction sur tout le territoire communal.", "Où se situent les risques invoqués ? Un périmètre restreint aurait-il suffi ?", 2)
    if "non délimité" in f["territoire"] or "non lisible" in f["territoire"]: pt("Périmètre imprécis", "Une interdiction dont les limites ne sont pas lisibles ne permet pas au citoyen de savoir où il peut aller : imprécision et insécurité juridique.", "Le plan annexé existe-t-il ? A-t-il été publié avec l'arrêté ?", 2)
    if sig and fin and (fin - sig).days >= 3: pt("Durée de %d jours" % (fin - sig).days, "Une mesure de police doit être limitée au temps du risque ; un événement ponctuel ne justifie pas plusieurs jours.", "L'arrêté explique-t-il pourquoi le risque persiste au-delà de la journée ?", 2)
    if f["periode"] == "sans terme fixé": pt("Mesure sans terme", "Une restriction de liberté sans limite de durée est en principe illégale.", "Le texte prévoit-il une date ou une condition de fin ?", 3)
    if nb == 0: pt("Aucun considérant", "Les mesures de police qui restreignent une liberté doivent être motivées en droit et en fait (art. L. 211-2 et L. 211-5 CRPA).", "La motivation est-elle dans un document distinct ?", 3)
    elif not circ: pt("Motivation de pure forme", "Le juge écarte les motivations générales (\"risques de troubles\") non étayées par des faits précis.", "Quels faits concrets, datés, l'administration peut-elle produire ?", 2)
    if f["base_legale"].startswith("aucune"): pt("Base légale non citée", "Sans visa de la base légale, incompétence ou erreur de droit possibles.", "Quel texte l'autorité pouvait-elle invoquer, et l'a-t-elle fait ailleurs ?", 2)
    if sig and ds:
        debut = min((d for d in ds if d >= sig), default=None)
        if debut and (debut - sig).days <= 1: pt("Signé la veille ou le jour même", "Publication tardive : prive du temps utile pour saisir le juge, ce qui pèse dans l'urgence du référé et peut constituer un vice de publicité.", "Date et mode de publication réels (RAA, affichage, site) ?", 2)
    if "captation" in f["mesure"]: pt("Captation par aéronef", "L'art. L. 242-5 CSI impose finalité précise, durée et périmètre strictement nécessaires, information du public, et absence d'autre moyen.", "L'arrêté justifie-t-il chacune de ces conditions ?", 2)
    if "dissimulation" in f["mesure"]: pt("Dissimulation du visage", "Interdiction admise seulement si limitée dans le temps et l'espace et justifiée par des risques précis.", "Périmètre, durée, motifs propres à cette mesure ?", 1)
    if "mineurs" in f["mesure"]: pt("Couvre-feu des mineurs", "Exige une motivation spécifique au risque pour les mineurs, des horaires et un périmètre adaptés.", "Faits propres aux mineurs cités ?", 2)
    P.sort(key=lambda x: -x["poids"])
    score = sum(x["poids"] for x in P)
    f["score"] = "fort" if score >= 6 else ("moyen" if score >= 3 else "faible")
    f["verdict"] = {"fort": "Intérêt à attaquer : fort (plusieurs fragilités sérieuses)", "moyen": "Intérêt à attaquer : moyen (à examiner sur pièces)", "faible": "Intérêt à attaquer : faible en l'état (acte apparemment ciblé et motivé)"}[f["score"]]
    return f

def points_attaque(b, sig, ds, fin):
    """Version courte (liste de phrases) pour les affichages compacts."""
    f = fiche_acte(b, sig, ds, fin)
    return [f["verdict"]] + ["%s : %s" % (x["titre"], x["pourquoi"]) for x in f["points"]][:7]

# ---------------------------------------------------------------- Classification des actes préfectoraux
# Deux étages : (1) nature de l'acte, par catégories fermées entrant dans l'objet (article 2 des statuts) ;
# (2) exclusions par catégorie. Un acte est retenu s'il entre dans une catégorie positive et dans aucune exclusion.
CATEGORIES = [
    ("manifestation", "interdiction ou restriction de manifestation, rassemblement, cortège ou attroupement",
     r"interdi\w+[^.\n]{0,120}(manifest|rassemblement|cort[eè]ge|attroupement|r[ée]union sur la voie publique)|(manifest|rassemblement|cort[eè]ge|attroupement)\w*[^.\n]{0,80}(interdi|prohib)|(r[ée]glement|restri|encadr)\w*[^.\n]{0,60}(manifestation|rassemblement|cort[eè]ge)|mesures? de police[^.\n]{0,60}(manifestation|rassemblement|cort[eè]ge)|itin[ée]raire[^.\n]{0,40}(manifestation|cort[eè]ge|d[ée]fil[ée])|interdiction de s[ée]journer|interdiction de para[iî]tre"),
    ("perimetre", "périmètre de protection ou de sécurité (L. 226-1 CSI), zone interdite au public",
     r"p[ée]rim[eè]tre de (protection|s[ée]curit[ée])|l\.\s*226-1|zone[^.\n]{0,40}interdi\w+[^.\n]{0,40}(public|personnes|acc[eè]s)|interdiction d.acc[eè]s[^.\n]{0,60}(public|personnes)"),
    ("couvre_feu", "couvre-feu", r"couvre[- ]feu"),
    ("mineurs", "restriction de circulation des mineurs", r"mineurs? (non accompagn|de moins de)|circulation des mineurs"),
    ("drones", "captation d'images par caméras aéroportées ou mobiles (L. 242 CSI)",
     r"cam[ée]ras? (a[ée]roport[ée]e|install[ée]e[s]? sur (des |un )?(a[ée]ronef|drone)|embarqu[ée]e|pi[ée]ton|mobile)|captation[^.\n]{0,80}(images|a[ée]ronef|drone)|a[ée]ronefs? circulant sans personne|l\.\s*242-\d|drones?[^.\n]{0,60}(images|cam[ée]ra|captation|surveillance)"),
    ("distribution", "interdiction de distribution alimentaire, de mendicité ou d'occupation humanitaire de l'espace public",
     r"distribution[^.\n]{0,40}(gratuite|alimentaire|de nourriture|de repas|de denr[ée]es)|mendicit[ée]|station(nement)? (assise|allong)|occupation (abusive|prolong[ée]e)[^.\n]{0,40}(espace|voie) public"),
    ("objets_visage", "interdiction de port ou transport d'objets, d'artifices, de carburants, dissimulation du visage",
     r"dissimul\w+[^.\n]{0,30}visage|port[^.\n]{0,40}(d.objets?|d.armes? par destination|d.[ée]quipements? de protection)|transport[^.\n]{0,40}(carburant|substance|artifice|combustible)|artifices? de divertissement|engins? pyrotechnique"),
    ("fermeture_lieu", "fermeture ou interdiction d'un lieu de réunion, de culte ou de spectacle",
     r"fermeture[^.\n]{0,40}(lieu de culte|mosqu[ée]e|salle|lieu de r[ée]union|[ée]tablissement recevant du public)|interdiction[^.\n]{0,60}(spectacle|r[ée]union publique|conf[ée]rence|concert|projection)"),
    ("circulation_personnes", "interdiction de circulation ou de stationnement des personnes (hors circulation routière)",
     r"interdiction[^.\n]{0,40}(de circuler|de circulation)[^.\n]{0,40}(personnes?|pi[ée]tons?|public)|interdiction de (stationner|se tenir)[^.\n]{0,60}(personnes|public|groupes?)"),
]
CATEGORIES_RX = [(k, lib, re.compile(rx, re.I | re.S)) for k, lib, rx in CATEGORIES]
EXCLUSIONS = [
    ("nominatif", r"d[ée]l[ée]gation de (signature|pouvoir|fonction)|habilitation|agr[ée]ment|nomination|d[ée]signation|composition|commission|comit[ée]|conseil (d[ée]partemental|m[ée]dical)|tableau d.avancement|m[ée]daille|honorariat|subdélégation|portant (modification|renouvellement) de l.arr[êe]t[ée] (de|portant) (nomination|composition|d[ée]l[ée]gation)"),
    ("environnement", r"installation[s]? class[ée]e|icpe|[ée]olien|carri[eè]re|d[ée]chets|eau potable|assainissement|captage|zone humide|natura 2000|esp[eè]ces prot[ée]g[ée]es|d[ée]frichement|plan de pr[ée]vention des risques|catastrophe naturelle|s[ée]cheresse|restriction[s]? des usages de l.eau|brûlage|feux? de for[êe]t|emploi du feu"),
    ("chasse_peche", r"\bchasse\b|\bp[êe]che\b|gibier|louveterie|battue|nuisibles|esp[eè]ces susceptibles"),
    ("routier", r"s[ée]curit[ée] routi[eè]re|circulation routi[eè]re|limitation de vitesse|poids lourds|autoroute|\b(rn|rd|a)\s?\d{1,4}\b|route nationale|route d[ée]partementale|chauss[ée]e|d[ée]viation|transports? exceptionnels?|fourri[eè]re|auto-[ée]cole|permis de conduire|taxi|vtc|immatriculation"),
    ("evenement", r"manifestation (sportive|nautique|a[ée]rienne|motoris[ée]e|cycliste|p[ée]destre|[ée]questre)|course (cycliste|p[ée]destre|automobile|hippique)|rallye|trail|marathon|triathlon|randonn[ée]e|meeting a[ée]rien|feu d.artifice|fête (foraine|votive)|braderie|brocante|vide[- ]greniers?|vente au d[ée]ballage|foire|salon|march[ée] (de no[eë]l|hebdomadaire)"),
    ("securite_civile", r"temp[êe]te|vigilance (orange|rouge)|intemp[ée]ries|\bcrue|inondation|avalanche|canicule|risque (d.)?incendie|massifs? forestier|\bplages?\b|falaise|[ée]boulement|p[ée]ril imminent|plan (orsec|communal de sauvegarde)|survol"),
    ("sanitaire", r"grippe aviaire|influenza|[ée]pizootie|tuberculose|fi[eè]vre|zone r[ée]glement[ée]e[^.\n]{0,40}(aviaire|sanitaire)|abattage|cheptel|v[ée]t[ée]rinaire|moustique|d[ée]moustication|baignade|qualit[ée] des eaux"),
    ("urbanisme", r"permis de (construire|d[ée]molir|am[ée]nager)|d[ée]claration d.utilit[ée] publique|expropriation|enqu[êe]te publique|cessibilit[ée]|servitude|alignement|lotissement|plan local d.urbanisme|zone d.am[ée]nagement|remembrement|p[ée]ril|insalubrit[ée]|mise en demeure"),
    ("economie", r"d[ée]bit de boissons|licence (ii|iii|iv)|fermeture administrative[^.\n]{0,40}([ée]tablissement|bar|restaurant|commerce|discoth[eè]que)|tarif|subvention|redevance|dotation|budget|march[ée] public|appel d.offres|liquidation|ouverture dominicale|d[ée]rogation au repos"),
    ("administration", r"r[ée]gie|r[ée]gisseur|jury|[ée]lection|liste [ée]lectorale|bureau de vote|recensement|archives|domaine public (fluvial|maritime)|concession|convention|cahier des charges|statuts|dissolution|cr[ée]ation (d.un|de la|du) (syndicat|[ée]tablissement|groupement)|funéraire|fun[ée]raire|cr[ée]mation|inhumation|transport de corps"),
]
EXCLUSIONS_RX = [(k, re.compile(rx, re.I)) for k, rx in EXCLUSIONS]
POSITIVES_FORTES = {"manifestation", "perimetre", "couvre_feu", "mineurs", "drones", "distribution", "fermeture_lieu"}

def categoriser(titre, corps):
    """Catégories positives et exclusions d'un acte. Le titre (et l'article 1er) comptent d'abord ; le corps confirme."""
    tt = (titre or "")[:400]
    m = re.search(r"article\s*1(?:er)?\b.{0,1500}", corps, re.I | re.S)
    art1 = m.group(0) if m else corps[:1500]
    pos_t = [k for k, lib, rx in CATEGORIES_RX if rx.search(tt)]
    pos_a = [k for k, lib, rx in CATEGORIES_RX if rx.search(art1)]
    neg_t = [k for k, rx in EXCLUSIONS_RX if rx.search(tt)]
    pos = list(dict.fromkeys(pos_t + pos_a))
    # décision : catégorie positive dans le titre ou l'article 1er, et aucune exclusion dans le titre ;
    # exception : "objets_visage" et "circulation_personnes" seuls ne suffisent pas sans catégorie forte (sinon on retient les arrêtés de voirie)
    retenu = bool(pos) and not neg_t and bool(set(pos) & POSITIVES_FORTES or (pos_t and set(pos_t) - {"circulation_personnes"}))
    # un titre explicitement "manifestation / rassemblement" l'emporte sur une exclusion "evenement" seulement s'il s'agit d'une interdiction
    if not retenu and "manifestation" in pos_t and neg_t == ["evenement"] and re.search(r"interdi", tt, re.I) and not re.search(r"autoris|\bcourse\b|rallye|trail|marathon|triathlon|randonn", tt, re.I):
        retenu = True   # interdiction de rassemblement à l'occasion d'un événement (match, festival) : c'est bien notre objet
    return pos, neg_t, retenu

def decouper_raa(txt):
    """Coupe un recueil en actes : chaque bloc commence à un en-tête d'arrêté et contient des visas ou un article 1er
    (ce qui écarte le sommaire et les pages de garde). Renvoie des (titre, bloc)."""
    txt = txt.replace("\x0c", "\n")
    # en-tête d'acte : "ARRÊTÉ N° ..." / "ARRÊTÉ PRÉFECTORAL ..." / "Arrêté portant ..." ; jamais la ligne "ARRÊTE :" qui ouvre le dispositif
    ENTETE = r"(?:ARR[ÊE]T[ÉE]S?(?:\s+(?:PR[ÉE]FECTORAL|INTERPR[ÉE]FECTORAL|MUNICIPAL|CONJOINT|COMPL[ÉE]MENTAIRE|MODIFICATIF))?\s*(?:N\s*°|n\s*°|No\b|N\s*:|DU\b|D[ÉE]PARTEMENTAL|PORTANT|RELATIF|AUTORISANT|INTERDISANT|INSTITUANT|R[ÉE]GLEMENTANT|FIXANT|MODIFIANT|PRESCRIVANT|du\b|portant|relatif|autorisant|interdisant|instituant|r[ée]glementant|fixant|modifiant|prescrivant)|Arr[êe]t[ée]s?\b(?!\s*:))"
    parts = re.split(r"\n(?=[ \t]*" + ENTETE + r"[^\n]{0,220}\n)", txt)
    out = []
    for b in parts:
        if len(b) < 300: continue
        if not re.search(r"\b(vu|VU)\b[^\n]{0,120}\b(code|loi|d[ée]cret|article)|\barticle\s*1(?:er)?\b|ARR[ÊE]TE\s*:?\s*\n", b[:8000], re.I): continue   # sommaire, pages de garde
        head = b[:1800]
        titre = ""
        m = re.search(r"(?:ARR[ÊE]T[ÉE]|Arr[êe]t[ée])[^\n]{0,80}?\b(portant|relatif|relative|instituant|interdisant|autorisant|r[ée]glementant|prescrivant|fixant|modifiant|cr[ée]ant|ordonnant)\b(.{10,320}?)(?=\s*(?:Le pr[ée]fet|LE PR[ÉE]FET|La pr[ée]f[eè]te|LA PR[ÉE]F[EÈ]TE|Vu |VU |Article|ARTICLE|NOR\s*:|\n\s*\n))", head, re.S | re.I)
        if m: titre = (m.group(1) + m.group(2))
        else:
            m = re.search(r"\b(portant|relatif|relative|instituant|interdisant|autorisant|r[ée]glementant|prescrivant|fixant|modifiant)\b(.{10,320}?)(?=\s*(?:Le pr[ée]fet|LE PR[ÉE]FET|La pr[ée]f[eè]te|Vu |VU |Article|ARTICLE|\n\s*\n))", head, re.S | re.I)
            if m: titre = m.group(1) + m.group(2)
        if not titre: titre = b.strip().split("\n")[0]
        titre = re.sub(r"\s+", " ", titre).strip()[:300]
        out.append((titre, b))
    return out

def analyser_arretes(txt):
    """Découpe un recueil par acte, ne garde que ceux qui entrent dans l'objet, et qualifie chacun."""
    res = []
    aujourd_hui = NOW.date()
    for titre, b in decouper_raa(txt):
        pos, neg, retenu = categoriser(titre, b)
        if not retenu: continue
        ds = sorted(set(dates_dans(b[:8000])))
        sig = None
        mf = re.search(r"Fait\s+(?:à|a)\s+.{0,60}?,?\s*le\s+([^\n]{6,40})", b, re.I | re.S)
        if mf:
            dfs = dates_dans(mf.group(1))
            if dfs and dfs[0] <= aujourd_hui: sig = dfs[0]
        if sig is None:
            d0 = date_titre(titre)
            if d0: sig = dt.date.fromisoformat(d0)
        if sig is None: sig = next((d for d in reversed(ds) if d <= aujourd_hui and d.year >= aujourd_hui.year - 1), None)
        # période d'application : dates postérieures ou égales à la signature, dans le dispositif
        ma = re.search(r"article\s*1(?:er)?\b.{0,3000}", b, re.I | re.S)
        dd = sorted(set(dates_dans(ma.group(0)))) if ma else []
        apres = [d for d in dd if (not sig or d >= sig) and (d - aujourd_hui).days <= 400]
        fin = max(apres) if apres else None
        if fin and fin >= aujourd_hui:
            voie = "en vigueur jusqu'au %s : référé-liberté (L. 521-2 CJA) ou référé-suspension possibles" % fin.strftime("%d/%m/%Y")
        elif sig and (aujourd_hui - sig).days <= 62:
            lim = sig + dt.timedelta(days=60)
            voie = ("effets passés le %s ; " % fin.strftime("%d/%m/%Y") if fin else "") + "recours pour excès de pouvoir possible jusqu'au %s environ (deux mois)" % lim.strftime("%d/%m/%Y")
        elif sig:
            voie = "délai de recours probablement expiré (acte du %s)" % sig.strftime("%d/%m/%Y")
        else:
            voie = "dates non reconnues : à vérifier"
        f = fiche_acte(b, sig, ds, fin)
        f["categories"] = pos
        f["mesure"] = ", ".join(lib for k, lib, rx in CATEGORIES_RX if k in pos) or f["mesure"]
        res.append({"titre": objet_propre(titre), "date": sig.isoformat() if sig else "", "fin": fin.isoformat() if fin else "", "voie": voie, "categories": pos,
                    "extraits": extraits(b, 2), "analyse": [f["verdict"]] + ["%s : %s" % (x["titre"], x["pourquoi"]) for x in f["points"]][:7], "fiche": f,
                    "contestable": bool(fin and fin >= aujourd_hui) or bool(sig and (aujourd_hui - sig).days <= 62)})
    return res

def pdf_texte(data):
    with tempfile.NamedTemporaryFile(suffix=".pdf", delete=False) as f:
        f.write(data); path = f.name
    try:
        r = subprocess.run(["pdftotext", "-layout", "-l", "60", path, "-"], capture_output=True, timeout=90)
        return r.stdout.decode("utf-8", "replace")
    except Exception:
        return ""
    finally:
        os.unlink(path)

def parse_rss(xml):
    try: root = ET.fromstring(xml.encode("utf-8") if isinstance(xml, str) else xml)
    except ET.ParseError: return []
    items = []
    for it in root.iter():
        if it.tag.split("}")[-1] not in ("item", "entry"): continue
        g = lambda *names: next((html.unescape(re.sub(r"<[^>]+>", " ", (c.text or ""))).strip() for c in it if c.tag.split("}")[-1] in names and c.text), "")
        link = g("link") or next((c.get("href", "") for c in it if c.tag.split("}")[-1] == "link"), "")
        items.append({"titre": g("title"), "url": link, "desc": g("description", "summary", "content"), "date": g("pubDate", "published", "updated", "date")})
    return items

def liens_pdf(page, base):
    out = {}
    for m in re.finditer(r'href="([^"]+?\.pdf)"[^>]*>(.*?)</a>', page, re.I | re.S):
        u = urllib.parse.urljoin(base, html.unescape(m.group(1)))
        t = html.unescape(re.sub(r"<[^>]+>", " ", m.group(2))).strip() or os.path.basename(u)
        out[u] = re.sub(r"\s+", " ", t)
    return out

def page_raa(host):
    """Trouve la page du recueil des actes administratifs et les PDF récents (profondeur 2)."""
    urls, pdfs = set(), {}
    for cand in ("/Publications/Recueil-des-actes-administratifs", "/Publications/Recueils-des-actes-administratifs", "/Publications/RAA", "/Publications/Recueil-des-Actes-Administratifs-RAA"):
        urls.add(f"https://{host}{cand}")
    pub = get(f"https://{host}/Publications")
    if pub:
        for m in re.finditer(r'href="([^"]+)"[^>]*>([^<]*recueil[^<]*actes[^<]*)</a>', pub, re.I):
            urls.add(urllib.parse.urljoin(f"https://{host}/", html.unescape(m.group(1))))
    vus = set()
    for u in list(urls)[:6]:
        p = get(u)
        if not p: continue
        vus.add(u); pdfs.update(liens_pdf(p, u))
        # sous-pages de l'année en cours (dossiers mensuels)
        for m in re.finditer(r'href="([^"]+)"[^>]*>([^<]*(?:%d|%s)[^<]*)</a>' % (NOW.year, NOW.strftime("%B")), p, re.I):
            su = urllib.parse.urljoin(u, html.unescape(m.group(1)))
            if su in vus or ".pdf" in su.lower(): continue
            vus.add(su); sp = get(su)
            if sp: pdfs.update(liens_pdf(sp, su))
            if len(vus) > 10: break
    return pdfs

def collecte_prefecture(dep, host):
    res = {"dep": dep, "host": host, "rss_ok": 0, "rss_items": [], "pdfs": {}}
    flux = {f"https://{host}/syndication/flux/rss_feed_69": "Actualités", f"https://{host}/syndication/flux/rss_feed_66": "Publications"}
    lx = get(f"https://{host}/syndication/listexport")
    if lx:
        for m in re.finditer(r'href="([^"]*?/syndication/flux/rss_feed_\d+)"[^>]*>([^<]*)<', lx, re.I):
            t = html.unescape(m.group(2)).strip()
            if re.search(r"arr[êe]t|recueil|actes administratifs|presse|communiqu|s[ée]curit|ordre public", t, re.I):
                flux[urllib.parse.urljoin(f"https://{host}/", m.group(1))] = t
    for u, titre in flux.items():
        x = get(u)
        if not x: continue
        res["rss_ok"] += 1
        for it in parse_rss(x):
            it["flux"] = titre; res["rss_items"].append(it)
    res["pdfs"] = page_raa(host)
    return res

def collecte_commune(c):
    """Page d'actes d'une commune : PDF nouveaux (profondeur 1 sur les sous-pages de l'année), lecture par navigateur si la page l'exige."""
    res = {"dep": str(c.get("departement", "")), "host": urllib.parse.urlsplit(c["url"]).netloc, "rss_ok": 0, "rss_items": [], "pdfs": {}, "commune": c["commune"], "autorite": c.get("autorite", "Maire de " + c["commune"])}
    urls = [c["url"]] + list(c.get("urls_secondaires") or [])
    if c.get("rss"):
        x = get(c["rss"])
        if x:
            res["rss_ok"] += 1
            for it in parse_rss(x): it["flux"] = "Actualités " + c["commune"]; res["rss_items"].append(it)
    if c.get("type") == "api_json":
        j = get(c["url"], timeout=40)
        try: d = json.loads(j or "{}")
        except Exception: d = {}
        recs = d.get("results") or d.get("records") or []
        res["rss_ok"] += 1 if recs else 0
        for r0 in recs:
            f = r0.get("record", {}).get("fields", r0) if isinstance(r0, dict) else {}
            titre = " ".join(str(f.get(k, "")) for k in ("objet", "titre", "title", "libelle", "intitule", "nom") if f.get(k))
            lien = next((str(v) for k, v in f.items() if isinstance(v, str) and v.lower().startswith("http") and ".pdf" in v.lower()), "")
            if not lien:
                for v in f.values():
                    if isinstance(v, dict) and str(v.get("url", "")).lower().endswith(".pdf"): lien = v["url"]; break
            if lien and pertinent_commune(titre or lien): res["pdfs"][lien] = titre or os.path.basename(lien)
        log(f"Commune {c['commune']} (api_json) : {len(res['pdfs'])} acte(s) pertinent(s) sur l'API")
        return res
    for u in urls[:4]:
        page = get(u)
        if page is None or c.get("type") in ("portail_js", "liste_paginee", "inconnu") and len(liens_pdf(page or "", u)) < 3:
            try:
                from playwright.sync_api import sync_playwright
                with sync_playwright() as p:
                    b = p.chromium.launch(args=["--no-sandbox"]); pg = b.new_context(user_agent=UA, locale="fr-FR").new_page()
                    pg.goto(u, timeout=45000, wait_until="networkidle"); pg.wait_for_timeout(2500); page = pg.content(); b.close()
            except Exception as e:
                log(c["commune"], ": page inaccessible :", str(e)[:100]); continue
        res["rss_ok"] += 1
        res["pdfs"].update(liens_pdf(page, u))
        for m in re.finditer(r'href="([^"]+)"[^>]*>([^<]*(?:%d|%s)[^<]*)</a>' % (NOW.year, NOW.strftime("%B")), page, re.I):
            su = urllib.parse.urljoin(u, html.unescape(m.group(1)))
            if ".pdf" in su.lower() or su in urls: continue
            sp = get(su)
            if sp: res["pdfs"].update(liens_pdf(sp, su))
            if len(res["pdfs"]) > 400: break
    log(f"Commune {c['commune']} ({c.get('type','')}) : {'page lue' if res['rss_ok'] else 'PAGE NON LUE'}, {len(res['pdfs'])} PDF trouvé(s)")
    return res

def collecte_paris():
    """Préfecture de police de Paris : site protégé contre les robots simples. Trois tentatives :
    RSS direct, navigateur invisible (Playwright) sur les actualités et le recueil des actes, et le widget public de X (@prefpolice)."""
    host = "www.prefecturedepolice.interieur.gouv.fr"
    res = {"dep": "75", "host": host, "rss_ok": 0, "rss_items": [], "pdfs": {}}
    x = get(f"https://{host}/rss/actualites.xml")
    if x and "requires JS enabled and cookies" not in x[:2000] and ("<rss" in x[:500] or "<feed" in x[:500]):
        res["rss_ok"] += 1
        for it in parse_rss(x): it["flux"] = "Actualités PP (RSS)"; res["rss_items"].append(it)
    else:
        log("Préfecture de police : RSS bloqué, passage par navigateur")
        try:
            from playwright.sync_api import sync_playwright
            with sync_playwright() as p:
                b = p.chromium.launch(args=["--no-sandbox"]); ctx = b.new_context(user_agent=UA, locale="fr-FR"); pg = ctx.new_page()
                pages = [(f"https://{host}/actualites-et-presse/actualites", "Actualités PP (navigateur)"),
                         (f"https://{host}/recueil-des-actes-administratifs", "RAA PP (navigateur)")]
                for u, titre in pages:
                    try:
                        pg.goto(u, timeout=45000, wait_until="domcontentloaded"); pg.wait_for_timeout(4000)
                        html_ = pg.content()
                        if "requires JS enabled and cookies" in html_[:3000]: log("Préfecture de police : protection toujours active sur", u); continue
                        res["rss_ok"] += 1
                        for pu, pt in liens_pdf(html_, u).items():
                            res["pdfs"][pu] = pt
                        for m in re.finditer(r'<a[^>]+href="([^"]+)"[^>]*>([^<]{15,200})</a>', html_):
                            t = html.unescape(m.group(2)).strip()
                            if re.search(r"arr[êe]t|manifest|interdiction|p[ée]rim[eè]tre|drone|rassemblement", t, re.I):
                                res["rss_items"].append({"titre": t, "url": urllib.parse.urljoin(u, m.group(1)), "desc": "", "date": "", "flux": titre})
                    except Exception as e:
                        log("Préfecture de police, navigateur :", str(e)[:120])
                b.close()
        except Exception as e:
            log("Playwright indisponible :", str(e)[:120])
    # Widget public X : derniers messages de @prefpolice
    try:
        xw = get("https://syndication.twitter.com/srv/timeline-profile/screen-name/prefpolice", timeout=20)
        if xw and "prefpolice" in xw:
            n = 0
            for m in re.finditer(r'"full_text":"(.*?)"(?:,|})', xw):
                txt = m.group(1).encode("utf-8").decode("unicode_escape", "ignore").replace("\\n", " ")
                if re.search(r"arr[êe]t|interdiction|manifest|p[ée]rim[eè]tre|drone|a[ée]ronef|rassemblement", txt, re.I):
                    res["rss_items"].append({"titre": txt[:200], "url": "https://x.com/prefpolice", "desc": txt, "date": "", "flux": "X @prefpolice"}); n += 1
            res["rss_ok"] += 1; log(f"X @prefpolice : widget lu, {n} message(s) pertinent(s)")
        else:
            log("X @prefpolice : widget indisponible")
    except Exception as e:
        log("X @prefpolice :", str(e)[:120])
    return res

def raa_datagouv(vus):
    """Nouveaux recueils recensés par data.gouv (hebdomadaire) : complète la lecture directe des pages RAA."""
    out = []
    for page in range(1, RAA_PAGES + 1):
        j = get(f"{RAA_API}?mise_a_jour__sort=desc&page_size=50&page={page}", timeout=30)
        if not j: log("data.gouv : API injoignable (page %d)" % page); break
        try: d = json.loads(j)
        except Exception: break
        for r in d.get("data", []):
            u = (r.get("url") or "").strip()
            if u and u not in vus: out.append((str(r.get("departement", "")), urllib.parse.urlsplit(u).netloc, u, re.sub(r"\s+", " ", r.get("titre") or "")))
        if not d.get("links", {}).get("next"): break
    log(f"data.gouv : {len(out)} recueil(s) non encore vus")
    return out

def pdfs_depuis_page(url):
    """Suit un lien d'actualité RSS et renvoie les PDF qu'il référence (arrêtés joints)."""
    if not url or url.lower().endswith(".pdf"): return {url: os.path.basename(url)} if url else {}
    page = get(url)
    return liens_pdf(page, url) if page else {}

def notifier_site(nouveaux):
    """Alerte courriel envoyée par le site lui-même (admin/notifier.php), si le jeton est fourni."""
    if not NOTIF_CLE or not nouveaux: return
    try:
        corps = json.dumps({"items": [{k: it.get(k, "") for k in ("departement", "date", "titre", "voie", "url", "analyse", "fiche")} for it in nouveaux[:30]]}).encode("utf-8")
        req = urllib.request.Request(f"{SITE}/admin/notifier.php?cle={urllib.parse.quote(NOTIF_CLE)}", data=corps, headers={"Content-Type": "application/json", "User-Agent": UA})
        with urllib.request.urlopen(req, timeout=20) as r: log("notifier.php :", r.read(200).decode("utf-8", "replace").strip())
    except Exception as e:
        log("notifier.php :", e)

def expirer(registre):
    """Passe en 'expiré' les actes publiés 'à contester' dont le délai est dépassé ; efface les détectés jamais publiés et expirés."""
    n = 0; auj = NOW.date()
    for r in list(registre):
        if r.get("publie") is False:
            d = r.get("date") or ""; fin = r.get("fin") or ""
            try:
                dd = dt.date.fromisoformat(d) if d else None; dfin = dt.date.fromisoformat(fin) if fin else None
            except ValueError:
                continue
            if dd and (auj - dd).days > 62 and not (dfin and dfin >= auj):
                registre.remove(r); n += 1
    for r in registre:
        if (r.get("statut") or "à contester") != "à contester": continue
        fin = r.get("fin") or ""; d = r.get("date") or ""
        try:
            dfin = dt.date.fromisoformat(fin) if fin else None
            dd = dt.date.fromisoformat(d) if d else None
        except ValueError:
            continue
        if dfin and dfin >= auj: continue
        if dd and (auj - dd).days > 62 and not (dfin and dfin >= auj):
            r["statut"] = "expiré"; n += 1
    return n

def ftp_connect():
    for cls in (FTP_TLS, FTP):
        try:
            f = cls(FTP_HOST, timeout=60); f.login(FTP_USER, FTP_PASS)
            if cls is FTP_TLS: f.prot_p()
            return f
        except Exception as e:
            log("FTP", cls.__name__, "échec :", e)
    return None

def ftp_put(f, remote, data):
    f.storbinary("STOR " + remote, io.BytesIO(data))

def ftp_cd_data(f):
    """Se place dans le dossier data du site, quel que soit le point d'entrée du compte FTP (racine, public_html, domaine)."""
    for d in (FTP_DIR + "/data", "data", "/data", "public_html/data", "/public_html/data", FTP_DIR.strip("/") + "/data"):
        try: f.cwd(d); return True
        except Exception: pass
    try:
        for n in f.nlst():
            if n.endswith("public_html") or "domains" in n:
                for d in (n + "/data", n + "/public_html/data"):
                    try: f.cwd(d); return True
                    except Exception: pass
    except Exception: pass
    log("FTP : dossier data introuvable (FTP_DIR =", FTP_DIR, ") ; racine vue :", f.pwd() if f else "?")
    return False

def ftp_get(f, remote):
    """Contenu d'un fichier du site (None s'il n'existe pas ou si la lecture échoue)."""
    buf = io.BytesIO()
    try: f.retrbinary("RETR " + remote, buf.write); return buf.getvalue().decode("utf-8", "replace")
    except error_perm: return None
    except Exception as e: log("FTP lecture", remote, ":", e); return None

def lire_site(f, nom, defaut):
    """Lit data/<nom> par FTP, sinon par la page de secours admin/donnees.php (jeton NOTIF_CLE), sinon en HTTP public.
    Renvoie (objet, lu) : lu=False signifie qu'on n'écrira pas ce fichier."""
    txt = ftp_get(f, nom) if f else None
    if txt is None and NOTIF_CLE:
        txt = get(f"{SITE}/admin/donnees.php?cle={urllib.parse.quote(NOTIF_CLE)}&f={nom}")
        if txt is not None and txt.lstrip().startswith('{"erreur"'): txt = None
    if txt is None: txt = get(f"{SITE}/data/{nom}")
    if txt is None: return defaut, False
    try: o = json.loads(txt)
    except Exception: return defaut, False
    return (o if isinstance(o, type(defaut)) else defaut), True

def notifier(titre, corps, url=""):
    if not NTFY: return
    try:
        req = urllib.request.Request(f"https://ntfy.sh/{NTFY}", data=corps.encode("utf-8"), headers={"Title": titre.encode("latin-1", "replace").decode("latin-1"), "Priority": "high", "Tags": "rotating_light", **({"Click": url} if url else {})})
        urllib.request.urlopen(req, timeout=15)
    except Exception as e:
        log("ntfy :", e)

def preparer_navigateur():
    """Installe Playwright et Chromium si absents (machine GitHub neuve à chaque passage, environ 40 s)."""
    try:
        import playwright.sync_api  # noqa
        return True
    except ImportError:
        pass
    log("Installation du navigateur invisible...")
    try:
        r0 = subprocess.run([sys.executable, "-m", "pip", "install", "-q", "--upgrade", "playwright"], timeout=300, capture_output=True, text=True)
        if r0.returncode != 0:
            log("pip (playwright) :", (r0.stderr or r0.stdout)[-300:])
            r0 = subprocess.run([sys.executable, "-m", "pip", "install", "-q", "--user", "playwright"], timeout=300, capture_output=True, text=True)
        import site, importlib; importlib.invalidate_caches()
        for sp in site.getsitepackages() + [site.getusersitepackages()]:
            if sp not in sys.path: sys.path.append(sp)
        r = subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"], check=False, timeout=600, capture_output=True, text=True)
        if r.returncode != 0:
            r = subprocess.run([sys.executable, "-m", "playwright", "install", "chromium"], check=False, timeout=600, capture_output=True, text=True)
        import importlib; importlib.invalidate_caches()
        import playwright.sync_api  # noqa
        log("Navigateur invisible prêt." if r.returncode == 0 else "Navigateur installé sans dépendances système : " + (r.stderr or "")[-200:])
        return True
    except Exception as e:
        log("Navigateur invisible indisponible :", str(e)[:160]); return False

def recent_doc(u, t):
    """Vrai si le document semble dater de moins de 70 jours (date dans le titre ou l'URL), ou si aucune date n'est lisible."""
    d = date_titre(t) or date_titre(u.replace("%20", " "))
    if d:
        try: return (NOW.date() - dt.date.fromisoformat(d)).days <= 70
        except Exception: return True
    ym = re.search(r"/(20\d\d)/(\d{2})[-_/]", u) or re.search(r"(20\d\d)[-_](\d{2})(?!\d)", u + " " + t)
    if ym:
        y, m = int(ym.group(1)), int(ym.group(2))
        if 1 <= m <= 12: return (NOW.year - y) * 12 + (NOW.month - m) <= 2
    ys = re.findall(r"\b(20[12]\d)\b", u + " " + t)
    if ys: return max(int(y) for y in ys) >= NOW.year
    mois = {"janvier":1,"fevrier":2,"février":2,"mars":3,"avril":4,"mai":5,"juin":6,"juillet":7,"aout":8,"août":8,"septembre":9,"octobre":10,"novembre":11,"decembre":12,"décembre":12}
    for k, v in mois.items():
        if re.search(r"\b" + k + r"\b", (u + " " + t).lower()): return (NOW.month - v) % 12 <= 2
    return True

def main():
    preparer_navigateur()
    prefs = json.loads(open("prefectures.json", encoding="utf-8").read()); prefs.pop("_commentaire", None)
    f0 = None
    for essai in range(3):   # le FTP de l'hébergeur ne répond pas toujours du premier coup
        f0 = ftp_connect() if FTP_HOST else None
        if f0 and ftp_cd_data(f0): break
        if f0:
            try: f0.quit()
            except Exception: pass
        f0 = None
        if not FTP_HOST: break
        log(f"FTP : lecture impossible (essai {essai + 1}/3), nouvelle tentative dans 10 s"); time.sleep(10)
    etat, etat_lu = lire_site(f0, "veille.json", {})
    registre, registre_lu = lire_site(f0, "arretes.json", [])
    journal0, journal_lu = lire_site(f0, "journal-public.json", [])
    if not etat_lu and FTP_HOST:
        sys.exit("ARRÊT : la mémoire de la veille (veille.json) est illisible par FTP et par la page de secours ; rien n'est écrit pour ne pas effacer l'existant. Vérifier FTP_HOST/FTP_DIR et le secret NOTIF_CLE.")
    decisions, _ = lire_site(f0, "decisions.json", [])
    etat_prec, _ = lire_site(f0, "etat-veille.json", {})
    if f0:
        try: f0.quit()
        except Exception: pass
    if not registre_lu: log("ATTENTION : registre (arretes.json) illisible, il ne sera pas modifié ce passage.")
    if not isinstance(etat.get("items"), list): etat["items"] = []
    if not isinstance(etat.get("sites"), dict): etat["sites"] = {}
    if not isinstance(etat.get("raa_vus"), list): etat["raa_vus"] = []
    connus = {i["id"]: i for i in etat["items"] if isinstance(i, dict) and i.get("id")}
    vus = set(etat.get("raa_vus", []))
    nouveaux = []
    t0 = time.time()
    try: communes = json.loads(open("communes.json", encoding="utf-8").read())
    except Exception: communes = []
    communes = [c for c in communes if isinstance(c, dict) and c.get("url")]
    with cf.ThreadPoolExecutor(max_workers=10) as ex:
        futs = [ex.submit(collecte_prefecture, d, h) for d, h in prefs.items() if d != "75"] + [ex.submit(collecte_paris)] + [ex.submit(collecte_commune, c) for c in communes]
        resultats = [f.result() for f in cf.as_completed(futs)]
    log(f"Communes surveillées : {len(communes)}")
    log(f"Collecte : {len(resultats)} sites en {time.time()-t0:.0f}s")
    pref_ok = [r for r in resultats if not r.get("commune") and (r.get("rss_ok") or r.get("pdfs"))]
    pref_ko = [r for r in resultats if not r.get("commune") and not (r.get("rss_ok") or r.get("pdfs"))]
    motifs = {}
    for r in pref_ko: motifs[ERREURS.get(r.get("host", ""), "réponse vide")] = motifs.get(ERREURS.get(r.get("host", ""), "réponse vide"), 0) + 1
    log(f"Préfectures : {len(pref_ok)} jointes, {len(pref_ko)} sans flux ni document" + (" : " + ", ".join(f"{k} ×{v}" for k, v in sorted(motifs.items(), key=lambda x: -x[1])) if motifs else ""))
    if pref_ko: log("   sans réponse : " + ", ".join(sorted(r["dep"] for r in pref_ko)[:101]))
    a_lire = []
    for r in sorted(resultats, key=lambda x: x["dep"]):
        etat.setdefault("sites", {})[r["dep"]] = {"hote": r["host"], "flux_ok": r["rss_ok"], "pdf_trouves": len(r["pdfs"]), "derniere_verif": NOW.strftime("%Y-%m-%d %H:%M")}
        for it in r["rss_items"]:
            if not pertinent_rss(it["titre"] + " " + it["desc"]): continue
            iid = hashlib.sha1((it["url"] or it["titre"]).encode()).hexdigest()[:16]
            if iid in connus: continue
            # les PDF joints à l'actualité seront lus comme des recueils
            for pu, pt in pdfs_depuis_page(it["url"]).items():
                if pu not in vus: vus.add(pu); a_lire.append((r["dep"], r["host"], pu, pt or it["titre"], r.get("commune", ""), r.get("autorite", "")))
            d = ""
            try: d = dt.datetime.strptime(it["date"][:25].strip(), "%a, %d %b %Y %H:%M:%S").strftime("%Y-%m-%d")
            except Exception: d = date_titre(it["titre"]) or NOW.strftime("%Y-%m-%d")
            item = {"id": iid, "departement": r["dep"], "hote": r["host"], "flux": it["flux"], "date": d, "titre": it["titre"], "resume": it["desc"][:400], "url": it["url"], "detecte_le": NOW.strftime("%Y-%m-%d %H:%M")}
            connus[iid] = item; nouveaux.append(item)
        for u, t in r["pdfs"].items():
            if u in vus: continue
            vus.add(u); a_lire.append((r["dep"], r["host"], u, t, r.get("commune", ""), r.get("autorite", "")))
    for x in raa_datagouv(vus):
        vus.add(x[2]); a_lire.append(x + ("", ""))
    anciens = [x for x in a_lire if not recent_doc(x[2], x[3] or "")]
    a_lire = [x for x in a_lire if recent_doc(x[2], x[3] or "")]
    for x in anciens: vus.add(x[2])   # documents datés de plus de 70 jours : hors délai de recours, jamais lus
    def _cle(x):
        d = date_titre(x[3] or "") or date_titre(x[2].replace("%20", " "))
        return (d or "0000-00-00", 1 if not x[4] else 0)   # les plus récents d'abord, préfectures avant communes à date égale
    a_lire.sort(key=_cle, reverse=True)
    quota, repartis, reste_q = {}, [], []
    for x in a_lire:
        k = x[4] or x[0]
        if quota.get(k, 0) < 12: quota[k] = quota.get(k, 0) + 1; repartis.append(x)
        else: reste_q.append(x)
    a_lire = repartis + reste_q
    log(f"PDF nouveaux à lire : {len(a_lire)} récents (max {MAX_PDF} ce passage), {len(anciens)} anciens écartés sans lecture")
    reste = a_lire[MAX_PDF:]
    stats = {"docs_lus": 0, "actes_retenus": 0, "retrogrades": 0, "illisibles": 0, "sans_objet": 0, "telecharges": 0}
    # Apprentissage : catégories que l'association écarte presque toujours (au moins 5 décisions, 80 % d'écartés)
    cat_dec = {}
    for d in decisions if isinstance(decisions, list) else []:
        for k in d.get("categories") or []: cat_dec.setdefault(k, [0, 0]); cat_dec[k][0] += 1; cat_dec[k][1] += 1 if d.get("decision") == "ecarte" else 0
    CAT_FAIBLES = {k for k, (n, e) in cat_dec.items() if n >= 5 and e / n >= 0.8}
    if cat_dec: log("Apprentissage : %d décision(s) enregistrées ; catégories presque toujours écartées : %s" % (sum(n for n, e in cat_dec.values()), ", ".join(sorted(CAT_FAIBLES)) or "aucune"))
    for dep, host, u, t, commune, autorite in a_lire[:MAX_PDF]:
        data = get(propre(u), timeout=60, binary=True)
        if not data: vus.discard(u); continue
        stats["telecharges"] += 1
        txt = pdf_texte(data)
        if not txt: stats["illisibles"] += 1; continue
        if commune and not pertinent_commune(t + " " + txt): continue
        if not any(rx.search(txt) for k, lib, rx in CATEGORIES_RX): stats["sans_objet"] += 1; continue   # aucune catégorie de l'objet dans tout le document
        arretes = analyser_arretes(txt)
        blocs = decouper_raa(txt); nb_blocs = len(blocs)
        log(f"  lu : {commune or ('dép. ' + dep)} · {(t or os.path.basename(u))[:70]} · {len(txt)//1000} k car., {nb_blocs} acte(s) découpé(s), {len(arretes)} retenu(s)")
        if DIAG and not arretes:
            if nb_blocs:
                for bt, bb in blocs[:8]:
                    pos, neg, ok = categoriser(bt, bb)
                    log(f"      - {bt[:110]} | cat={pos} excl={neg}")
            elif len(txt) > 20000:
                tetes = [l.strip() for l in txt.split("\n") if re.search(r"arr[êe]t[ée]", l, re.I) and len(l.strip()) < 160][:8]
                log("      - aucun en-tête reconnu ; lignes contenant 'arrêté' : " + " || ".join(tetes))
        if not arretes: continue   # des mots de l'objet, mais aucun acte retenu après découpage et classification
        stats["actes_retenus"] += len(arretes); stats["docs_lus"] += 1
        for k, a in enumerate(arretes):
            if a.get("categories") and set(a["categories"]) <= CAT_FAIBLES:
                a["fiche"]["score"] = "faible"; a["fiche"]["verdict"] = "Intérêt à attaquer : faible (catégorie presque toujours écartée par l'association)"; a["contestable"] = False; stats["retrogrades"] += 1
            iid = hashlib.sha1((u + "#" + str(k)).encode()).hexdigest()[:16]
            if iid in connus: continue
            cle_titre = re.sub(r"[^a-z0-9]+", " ", (a["titre"] or t).lower()).strip()[:120]
            if any(re.sub(r"[^a-z0-9]+", " ", c.get("titre", "").lower()).strip()[:120] == cle_titre and c.get("departement") == dep for c in connus.values()): continue
            item = {"id": iid, "departement": dep, "hote": host, "flux": ("Arrêté municipal, " + commune) if commune else "RAA (contenu lu)", "commune": commune, "autorite_detectee": autorite,
                    "date": a["date"] or date_titre(t + " " + os.path.basename(u)) or NOW.strftime("%Y-%m-%d"), "fin": a.get("fin", ""),
                    "titre": a["titre"] or t, "recueil": t, "voie": a["voie"], "contestable": a["contestable"], "analyse": a.get("analyse", []), "fiche": a.get("fiche", {}),
                    "resume": a["voie"] + (" | " + " [...] ".join(a["extraits"]) if a["extraits"] else ""), "url": u, "detecte_le": NOW.strftime("%Y-%m-%d %H:%M")}
            connus[iid] = item; nouveaux.append(item)
    for x in reste: vus.discard(x[2])   # seront lus au prochain passage
    # registre automatique
    ajoutes = 0
    if AUTO_REGISTRE and nouveaux:
        urls = {x.get("url", "") for x in registre}
        for it in nouveaux:
            if not it["url"] or it["url"] in urls: continue
            dep = it["departement"]; nomdep = DEPARTEMENTS.get(dep, ("", ""))
            registre.append({"date": it["date"], "fin": it.get("fin", ""), "voie": it.get("voie", ""), "analyse": it.get("analyse", []), "fiche": it.get("fiche", {}), "commune": it.get("commune", ""), "departement": (dep + " - " + nomdep[0]) if nomdep[0] else dep,
                             "autorite": it.get("autorite_detectee") or ("Préfet de police" if dep == "75" else ("Préfet " + nomdep[1] if nomdep[1] else f"Préfet (département {dep})")),
                             "type": "Arrêté municipal" if it.get("commune") else ("Recueil des actes administratifs" if it["flux"].startswith("RAA") else "Publication préfectorale"),
                             "objet": objet_propre(it["titre"]), "resume": (it.get("resume") or "")[:600], "url": it["url"], "auto": True,
                             "statut": "à contester" if it.get("contestable", True) else "expiré", "publie": AUTO_PUBLIER, "detecte_le": it["detecte_le"]})
            urls.add(it["url"]); it["au_registre"] = True; ajoutes += 1
        registre.sort(key=lambda x: x.get("date", ""), reverse=True)
    nexp = expirer(registre)
    if nexp: log(f"Registre : {nexp} acte(s) passé(s) en 'expiré'")
    items = sorted(connus.values(), key=lambda i: (i.get("date", ""), i.get("detecte_le", "")), reverse=True)
    etat.update({"items": items, "raa_vus": sorted(vus)[-8000:], "derniere_execution": NOW.strftime("%Y-%m-%d %H:%M"), "nouveaux_derniere_execution": len(nouveaux), "collecteur": "github-actions"})
    public = [{k: i.get(k, "") for k in ("departement", "date", "fin", "titre", "voie", "resume", "url", "detecte_le", "flux")} for i in items[:200] if not i.get("ignore")]
    log(f"Documents téléchargés : {stats['telecharges']}, texte illisible : {stats['illisibles']}, sans mot de l'objet : {stats['sans_objet']}, avec au moins un acte retenu : {stats['docs_lus']}, actes retenus : {stats['actes_retenus']}, rétrogradés par apprentissage : {stats['retrogrades']}")
    log(f"Nouveaux : {len(nouveaux)}, ajoutés au registre : {ajoutes}, total veille : {len(items)}")
    # État public de la veille (bandeau du site) et journal public (page "Journal de veille")
    joints = sum(1 for r in resultats if r.get("rss_ok") or r.get("pdfs"))
    nb_pref = sum(1 for r in resultats if not r.get("commune")); nb_com = sum(1 for r in resultats if r.get("commune"))
    seuil24 = (NOW - dt.timedelta(hours=24)).strftime("%Y-%m-%d %H:%M")
    # état site par site, publié (département -> joint ou non, documents vus ; communes par nom)
    sites_pub = {}
    for r in resultats:
        ok = bool(r.get("rss_ok") or r.get("pdfs"))
        if r.get("commune"): sites_pub["c:" + r["commune"]] = {"joint": ok, "docs": len(r.get("pdfs") or {}), "dep": r.get("dep", "")}
        else: sites_pub[r["dep"]] = {"joint": ok, "docs": len(r.get("pdfs") or {}), "hote": r.get("host", "")}
    etat_public = {"derniere_execution": PARIS.strftime("%Y-%m-%d %H:%M"), "fuseau": "Europe/Paris", "prefectures": nb_pref, "communes": nb_com, "sites_joints": joints,
                   "detectes_passage": len(nouveaux), "detectes_24h": sum(1 for i in items if (i.get("detecte_le") or "") >= seuil24),
                   "total_veille": len(items), "source": "github-actions", "frequence_minutes": 30, "documents_lus": stats["docs_lus"], "actes_retenus": stats["actes_retenus"],
                   "pdf_lus_passage": min(len(a_lire), MAX_PDF), "sites": sites_pub}
    # cumuls depuis la création (repris du précédent état publié)
    cp = etat_prec.get("cumul") if isinstance(etat_prec, dict) and isinstance(etat_prec.get("cumul"), dict) else {}
    etat_public["cumul"] = {"depuis": cp.get("depuis") or PARIS.strftime("%Y-%m-%d"), "passages": int(cp.get("passages", 0)) + 1,
                            "documents_lus": int(cp.get("documents_lus", 0)) + min(len(a_lire), MAX_PDF), "actes_releves": int(cp.get("actes_releves", 0)) + len(nouveaux),
                            "sites_joints": int(cp.get("sites_joints", 0)) + joints}
    # mode : veille renforcée le vendredi soir et le samedi matin (créneaux habituels des arrêtés d'interdiction)
    wd, hh = PARIS.weekday(), PARIS.hour
    etat_public["mode"] = "renforcé" if (wd == 4 and 16 <= hh <= 22) or (wd == 5 and 7 <= hh <= 13) else "normal"
    etat_public["frequence_minutes"] = 15 if etat_public["mode"] == "renforcé" else (60 if 1 <= hh <= 5 else 30)
    journal = journal0
    injoignables = sorted([r["dep"] for r in resultats if not r.get("commune") and not (r.get("rss_ok") or r.get("pdfs"))]) + sorted([r["commune"] for r in resultats if r.get("commune") and not (r.get("rss_ok") or r.get("pdfs"))])
    evts = [{"quand": PARIS.strftime("%Y-%m-%d %H:%M"), "type": "passage", "texte": f"Passage de veille : {joints} sites joints sur {len(resultats)} ({nb_pref} préfectures, {nb_com} communes), {min(len(a_lire), MAX_PDF)} document{'s' if min(len(a_lire), MAX_PDF) > 1 else ''} lu{'s' if min(len(a_lire), MAX_PDF) > 1 else ''}, {len(nouveaux)} acte{'s' if len(nouveaux) > 1 else ''} relevé{'s' if len(nouveaux) > 1 else ''}.",
             "joints": joints, "total": len(resultats), "injoignables": injoignables[:40], "lus": min(len(a_lire), MAX_PDF), "releves": len(nouveaux), "duree_s": int(time.time() - t0)}]
    for it in [n for n in nouveaux if n.get("contestable", True)][:20]:
        lieu = it.get("commune") or f"département {it['departement']}"
        evts.append({"quand": PARIS.strftime("%Y-%m-%d %H:%M"), "type": "detection", "texte": f"Acte relevé, {lieu} : {it['titre'][:140]}", "url": it.get("url", ""), "dep": it["departement"], "commune": it.get("commune", ""), "date_acte": it.get("date", ""), "fin": it.get("fin", ""), "source": it.get("flux", "")})
    journal = (evts + journal)[:400]
    notifier_site([n for n in nouveaux if n.get("contestable", True)])
    for it in [n for n in nouveaux if n.get("contestable", True)][:10]:
        notifier(f"Dép. {it['departement']} : {it['titre'][:80]}", (it["resume"] or it["flux"])[:300], it["url"])
    if not FTP_HOST:
        log("FTP non configuré : résultats écrits localement dans sortie/"); os.makedirs("sortie", exist_ok=True)
        for n, o in [("veille.json", etat), ("veille-public.json", public), ("etat-veille.json", etat_public), ("journal-public.json", journal)] + ([("arretes.json", registre)] if registre_lu else []):
            open(f"sortie/{n}", "w", encoding="utf-8").write(json.dumps(o, ensure_ascii=False, indent=2))
        return
    f = ftp_connect()
    if not f: sys.exit("Connexion FTP impossible")
    if not ftp_cd_data(f): sys.exit("Dossier data introuvable sur le FTP : vérifier la variable FTP_DIR")
    sorties = [("veille.json", etat), ("veille-public.json", public), ("etat-veille.json", etat_public), ("journal-public.json", journal)]
    if registre_lu: sorties.append(("arretes.json", registre))   # arretes-public.json est produit par le site lors de la publication manuelle
    for n, o in sorties:
        ftp_put(f, n, (json.dumps(o, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    f.quit(); log("Envoyé sur le site.")

if __name__ == "__main__":
    main()
