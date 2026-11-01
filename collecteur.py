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
UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36"
MAX_PDF = int(os.environ.get("MAX_PDF", "80"))
MAX_AGE_DAYS = 45
NOW = dt.datetime.now(dt.timezone.utc)

FORTS = re.compile(r"interdiction de manifest|interdisant .{0,80}manifest|manifestation.{0,60}interdi|interdiction .{0,40}rassemblement|rassemblement.{0,60}interdi|interdiction .{0,40}cort[eè]ge|attroupement|couvre[- ]feu|p[ée]rim[eè]tre .{0,30}(interdiction|s[ée]curit[ée]|protection)|captation.{0,60}(images|a[ée]ronef|drone)|cam[ée]ras? .{0,30}a[ée]ronefs?|dissimulation du visage|mineurs non accompagn|interdiction .{0,60}circul|libert[ée] de manifest|aller et venir|d[ée]claration de manifestation", re.I | re.S)
BANALS = re.compile(r"manifestation sportive|course cycliste|rallye|trail|marathon|chasse|p[êe]che en|brûlage|feux? de for[êe]t|s[ée]cheresse|grippe aviaire|enqu[êe]te publique|ICPE|[ée]olien", re.I)
MOTS_RSS = ["manifestation", "manifester", "rassemblement", "cortège", "attroupement", "interdiction", "interdit", "périmètre", "couvre-feu", "drone", "aéronef", "captation", "caméra", "surveillance", "ordre public", "circulation", "liberté", "dissimulation du visage", "mineurs non accompagnés"]

def log(*a): print(*a, flush=True)

def get(url, timeout=25, binary=False):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "fr-FR,fr;q=0.9", "Accept": "*/*"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = r.read(25 * 1024 * 1024)
            return data if binary else data.decode(r.headers.get_content_charset() or "utf-8", "replace")
    except Exception as e:
        return None

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
    m = re.search(r"\b(\d{4})[-_](\d{2})[-_](\d{2})\b", t)
    if m and int(m.group(2)) <= 12: return f"{m.group(1)}-{m.group(2)}-{m.group(3)}"
    return ""

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

def analyser_arretes(txt):
    """Découpe le texte d'un recueil par arrêté et qualifie ceux qui restreignent une liberté."""
    blocs = re.split(r"\n(?=\s*(?:ARR[ÊE]T[ÉE]\s*(?:PR[ÉE]FECTORAL|N°|n°|DU)|Arr[êe]t[ée]\s+(?:pr[ée]fectoral\s+)?(?:n°|N°|du|portant)))", txt)
    res = []
    aujourd_hui = NOW.date()
    for b in blocs:
        if len(b) < 200 or not FORTS.search(b) or (BANALS.search(b[:600]) and not FORTS.search(b[:1500])): continue
        titre = re.sub(r"\s+", " ", b.strip().split("\n")[0])[:220]
        m = re.search(r"(?:portant|relatif à|instituant|interdisant|autorisant|réglementant)\s.{10,260}?(?=\s(?:Le |La |Vu |VU |Article|ARTICLE|\n))", b[:2500], re.S)
        if m: titre = re.sub(r"\s+", " ", m.group(0))[:260]
        ds = sorted(set(dates_dans(b[:6000])))
        sig = None
        mf = re.search(r"Fait\s+(?:à|a)\s+.{0,60}?,?\s*le\s+([^\n]{6,40})", b, re.I | re.S)
        if mf:
            dfs = dates_dans(mf.group(1))
            if dfs and dfs[0] <= aujourd_hui: sig = dfs[0]
        if sig is None: sig = next((d for d in reversed(ds) if d <= aujourd_hui), None)
        futures = [d for d in ds if d >= aujourd_hui]
        fin = max(ds) if ds else None
        if fin and fin >= aujourd_hui:
            voie = "en vigueur jusqu'au %s : référé-liberté (L. 521-2 CJA) ou référé-suspension possibles" % fin.strftime("%d/%m/%Y")
        elif sig and (aujourd_hui - sig).days <= 62:
            lim = sig + dt.timedelta(days=60)
            voie = "effets passés ; recours pour excès de pouvoir possible jusqu'au %s environ (délai de deux mois)" % lim.strftime("%d/%m/%Y")
        elif sig:
            voie = "délai de recours probablement expiré (acte du %s)" % sig.strftime("%d/%m/%Y")
        else:
            voie = "dates non reconnues : à vérifier"
        res.append({"titre": titre, "date": sig.isoformat() if sig else "", "fin": fin.isoformat() if fin else "", "voie": voie,
                    "extraits": extraits(b, 2), "analyse": points_attaque(b, sig, ds, fin), "fiche": fiche_acte(b, sig, ds, fin),
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
            try:
                from playwright.sync_api import sync_playwright
            except ImportError:
                log("Installation du navigateur invisible (une fois par passage)...")
                subprocess.run([sys.executable, "-m", "pip", "install", "-q", "playwright"], check=True, timeout=300)
                subprocess.run([sys.executable, "-m", "playwright", "install", "--with-deps", "chromium"], check=False, timeout=600, capture_output=True)
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
    """Passe en 'expiré' les actes 'à contester' dont le délai de recours est dépassé."""
    n = 0; auj = NOW.date()
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

def notifier(titre, corps, url=""):
    if not NTFY: return
    try:
        req = urllib.request.Request(f"https://ntfy.sh/{NTFY}", data=corps.encode("utf-8"), headers={"Title": titre.encode("latin-1", "replace").decode("latin-1"), "Priority": "high", "Tags": "rotating_light", **({"Click": url} if url else {})})
        urllib.request.urlopen(req, timeout=15)
    except Exception as e:
        log("ntfy :", e)

def main():
    prefs = json.loads(open("prefectures.json", encoding="utf-8").read()); prefs.pop("_commentaire", None)
    try: etat = json.loads(get(f"{SITE}/data/veille.json") or "{}")
    except Exception: etat = {}
    if not isinstance(etat, dict): etat = {}
    if not isinstance(etat.get("items"), list): etat["items"] = []
    if not isinstance(etat.get("sites"), dict): etat["sites"] = {}
    if not isinstance(etat.get("raa_vus"), list): etat["raa_vus"] = []
    try: registre = json.loads(get(f"{SITE}/data/arretes.json") or "[]")
    except Exception: registre = []
    if not isinstance(registre, list): registre = []
    connus = {i["id"]: i for i in etat["items"] if isinstance(i, dict) and i.get("id")}
    vus = set(etat.get("raa_vus", []))
    nouveaux = []
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=10) as ex:
        futs = [ex.submit(collecte_prefecture, d, h) for d, h in prefs.items() if d != "75"] + [ex.submit(collecte_paris)]
        resultats = [f.result() for f in cf.as_completed(futs)]
    log(f"Collecte : {len(resultats)} sites en {time.time()-t0:.0f}s")
    a_lire = []
    for r in sorted(resultats, key=lambda x: x["dep"]):
        etat.setdefault("sites", {})[r["dep"]] = {"hote": r["host"], "flux_ok": r["rss_ok"], "pdf_trouves": len(r["pdfs"]), "derniere_verif": NOW.strftime("%Y-%m-%d %H:%M")}
        for it in r["rss_items"]:
            if not pertinent_rss(it["titre"] + " " + it["desc"]): continue
            iid = hashlib.sha1((it["url"] or it["titre"]).encode()).hexdigest()[:16]
            if iid in connus: continue
            # les PDF joints à l'actualité seront lus comme des recueils
            for pu, pt in pdfs_depuis_page(it["url"]).items():
                if pu not in vus: vus.add(pu); a_lire.append((r["dep"], r["host"], pu, pt or it["titre"]))
            d = ""
            try: d = dt.datetime.strptime(it["date"][:25].strip(), "%a, %d %b %Y %H:%M:%S").strftime("%Y-%m-%d")
            except Exception: d = date_titre(it["titre"]) or NOW.strftime("%Y-%m-%d")
            item = {"id": iid, "departement": r["dep"], "hote": r["host"], "flux": it["flux"], "date": d, "titre": it["titre"], "resume": it["desc"][:400], "url": it["url"], "detecte_le": NOW.strftime("%Y-%m-%d %H:%M")}
            connus[iid] = item; nouveaux.append(item)
        for u, t in r["pdfs"].items():
            if u in vus: continue
            vus.add(u); a_lire.append((r["dep"], r["host"], u, t))
    for x in raa_datagouv(vus):
        vus.add(x[2]); a_lire.append(x)
    log(f"PDF nouveaux à lire : {len(a_lire)} (max {MAX_PDF} ce passage)")
    reste = a_lire[MAX_PDF:]
    for dep, host, u, t in a_lire[:MAX_PDF]:
        data = get(propre(u), timeout=60, binary=True)
        if not data: vus.discard(u); continue
        txt = pdf_texte(data)
        if not txt: continue
        if BANALS.search(txt) and not FORTS.search(txt): continue
        m = FORTS.search(txt)
        if not m: continue
        arretes = analyser_arretes(txt) or [{"titre": t, "date": "", "fin": "", "voie": "à qualifier", "extraits": extraits(txt), "contestable": True}]
        for k, a in enumerate(arretes):
            iid = hashlib.sha1((u + "#" + str(k)).encode()).hexdigest()[:16]
            if iid in connus: continue
            cle_titre = re.sub(r"[^a-z0-9]+", " ", (a["titre"] or t).lower()).strip()[:120]
            if any(re.sub(r"[^a-z0-9]+", " ", c.get("titre", "").lower()).strip()[:120] == cle_titre and c.get("departement") == dep for c in connus.values()): continue
            item = {"id": iid, "departement": dep, "hote": host, "flux": "RAA (contenu lu)",
                    "date": a["date"] or date_titre(t + " " + os.path.basename(u)) or NOW.strftime("%Y-%m-%d"), "fin": a.get("fin", ""),
                    "titre": a["titre"] or t, "recueil": t, "voie": a["voie"], "contestable": a["contestable"], "analyse": a.get("analyse", []), "fiche": a.get("fiche", {}),
                    "resume": a["voie"] + (" | " + " [...] ".join(a["extraits"]) if a["extraits"] else ""), "url": u, "detecte_le": NOW.strftime("%Y-%m-%d %H:%M")}
            connus[iid] = item; nouveaux.append(item)
    for dep, host, u, t in reste: vus.discard(u)   # seront lus au prochain passage
    # registre automatique
    ajoutes = 0
    if AUTO_REGISTRE and nouveaux:
        urls = {x.get("url", "") for x in registre}
        for it in nouveaux:
            if not it["url"] or it["url"] in urls: continue
            registre.append({"date": it["date"], "fin": it.get("fin", ""), "voie": it.get("voie", ""), "analyse": it.get("analyse", []), "fiche": it.get("fiche", {}), "commune": "", "departement": it["departement"],
                             "autorite": "Préfet de police" if it["departement"] == "75" else f"Préfet (département {it['departement']})",
                             "type": "Recueil des actes administratifs" if it["flux"].startswith("RAA") else "Publication préfectorale",
                             "objet": it["titre"] + (" : " + it["resume"][:300] if it["resume"] else ""), "url": it["url"], "auto": True,
                             "statut": "à contester" if it.get("contestable", True) else "expiré", "detecte_le": it["detecte_le"]})
            urls.add(it["url"]); it["au_registre"] = True; ajoutes += 1
        registre.sort(key=lambda x: x.get("date", ""), reverse=True)
    nexp = expirer(registre)
    if nexp: log(f"Registre : {nexp} acte(s) passé(s) en 'expiré'")
    items = sorted(connus.values(), key=lambda i: (i.get("date", ""), i.get("detecte_le", "")), reverse=True)
    etat.update({"items": items, "raa_vus": sorted(vus)[-8000:], "derniere_execution": NOW.strftime("%Y-%m-%d %H:%M"), "nouveaux_derniere_execution": len(nouveaux), "collecteur": "github-actions"})
    public = [{k: i.get(k, "") for k in ("departement", "date", "fin", "titre", "voie", "resume", "url", "detecte_le", "flux")} for i in items[:200] if not i.get("ignore")]
    log(f"Nouveaux : {len(nouveaux)}, ajoutés au registre : {ajoutes}, total veille : {len(items)}")
    notifier_site([n for n in nouveaux if n.get("contestable", True)])
    for it in [n for n in nouveaux if n.get("contestable", True)][:10]:
        notifier(f"Dép. {it['departement']} : {it['titre'][:80]}", (it["resume"] or it["flux"])[:300], it["url"])
    if not FTP_HOST:
        log("FTP non configuré : résultats écrits localement dans sortie/"); os.makedirs("sortie", exist_ok=True)
        for n, o in (("veille.json", etat), ("veille-public.json", public), ("arretes.json", registre)):
            open(f"sortie/{n}", "w", encoding="utf-8").write(json.dumps(o, ensure_ascii=False, indent=2))
        return
    f = ftp_connect()
    if not f: sys.exit("Connexion FTP impossible")
    f.cwd(FTP_DIR + "/data")
    for n, o in (("veille.json", etat), ("veille-public.json", public), ("arretes.json", registre)):
        ftp_put(f, n, (json.dumps(o, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    f.quit(); log("Envoyé sur le site.")

if __name__ == "__main__":
    main()
