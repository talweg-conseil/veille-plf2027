"""
Veille amendements PLF 2027 (texte n° 3210) - Talweg

Ce script :
  1. télécharge l'open data des amendements de l'Assemblée nationale (17e législature) ;
  2. garde les amendements déposés sur le PLF 2027 ;
  3. ne retient que ceux qui citent CIR, CII, crédit d'impôt collection ou JEI ;
  4. produit deux fichiers JSON lus par Make :
       data/amendements_plf2027.json : base complète filtrée
       data/delta.json               : amendements nouveaux ou modifiés récemment

Usage :
  python filtre_amendements.py                  (téléchargement automatique)
  python filtre_amendements.py chemin/vers.zip  (test sur un zip local)
"""

import datetime as dt
import difflib
import hashlib
import html
import json
import re
import sys
import tempfile
import time
import unicodedata
import zipfile
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# PARAMÈTRES (les seules lignes à modifier en temps normal)
# ---------------------------------------------------------------------------

URL_ZIP = ("https://data.assemblee-nationale.fr/static/openData/repository/"
           "17/loi/amendements_div_legis/Amendements.json.zip")
URL_DEPUTES = ("https://data.assemblee-nationale.fr/static/openData/repository/"
               "17/amo/deputes_actifs_mandats_actifs_organes/"
               "AMO10_deputes_actifs_mandats_actifs_organes.json.zip")
JOURS_DELTA = 0      # le delta ne contient que les changements du jour (0 = aujourd'hui seulement)
TAILLE_BLOC = 1900   # limite Notion : 2000 caractères par bloc de texte

DOSSIER = Path("data")
FICHIER_BASE = DOSSIER / "amendements_plf2027.json"
FICHIER_DELTA = DOSSIER / "delta.json"

# Textes suivis. Chaque texte a son propre périmètre de recherche.
#   credits_244 : recherche CIR, CII, CIC (article 244 quater B)
#   jei         : recherche le statut JEI et ses dérivés (JEIR, JEC, JEU)
#   commission_fond : préfixe des amendements de la commission saisie au fond
TEXTES = [
    {"num": "3210", "libelle": "PLF 2027", "prefixe_titre": "",
     "credits_244": True, "jei": True,
     "commission_fond": ("CF", "Commission des finances")},
    {"num": "3211", "libelle": "PLFSS 2027", "prefixe_titre": "PLFSS · ",
     "credits_244": False, "jei": True,
     "commission_fond": ("AS", "Commission des affaires sociales")},
]

# Expressions recherchées, APRÈS normalisation du texte :
# minuscules, sans accents, apostrophes droites, espaces simples.
MOTS_CREDITS = {
    "CIR": [r"credits? d'impot (en faveur de la )?recherche", r"\bcir\b", r"199 ter b"],
    "CII": [r"credits? d'impot (en faveur de l')?innovation", r"\bcii\b"],
    "CIC": [r"credits? d'impot collection", r"nouvelles collections"],
}
REF_244 = [r"244 quater b"]          # repère l'amendement ; CIR par défaut si aucun crédit nommé

MOTS_JEI = {
    "JEI": [r"jeunes? entreprises? innovantes?"],
    "JEIR": [r"jeunes? entreprises? d'innovation de rupture"],
    "JEC": [r"jeunes? entreprises? de croissance", r"jeunes? entreprises? innovantes? de croissance"],
    "JEU": [r"jeunes? entreprises? universitaires?"],
    "JEII": [r"jeunes? entreprises? d'innovation a impact"],
}
# Sigles : recherchés en MAJUSCULES uniquement (sinon "jeu" ou "en jeu" seraient captés)
SIGLES_JEI = {
    "JEI": [r"\bJEI\b"],
    "JEIR": [r"\bJEIR\b"],
    "JEC": [r"\bJEC\b", r"\bJEIC\b"],
    "JEU": [r"\bJEU\b"],
    "JEII": [r"\bJEII\b"],
}
# Références juridiques du statut : JEI par défaut si aucun régime n'est nommé
REF_JEI = [r"44 sexies-0 a",                  # définition de toutes les catégories (CGI)
           r"2003-1311",                      # art. 131 loi n° 2003-1311 (exonération sociale)
           r"199 terdecies-0 a bis"]          # réduction d'impôt des investisseurs JEI
REF_JEIR = [r"199 terdecies-0 a ter"]         # réduction d'impôt des investisseurs JEIR

# Filet pour un futur statut « jeune entreprise » encore inconnu :
#  - un sigle en JE + 1 à 4 majuscules qui n'est pas dans la liste connue (ex. « JES ») ;
#  - une formule de création de statut : « dites / dénommées / qualifiées de jeunes entreprises ... ».
SIGLES_CONNUS = {"JEI", "JEIR", "JEC", "JEIC", "JEU", "JEII"}
MOTS_MAJUSCULES_IGNORES = {"JEUX", "JEUNE", "JEUNES", "JEUDI", "JEAN", "JEANNE", "JET", "JETS", "JEE"}
SIGLE_JE = r"\bJE[A-Z]{1,4}\b"
FORMULES_NOUVEAU_STATUT = [r"(dites?|denommees?|qualifiees? de) \W{0,3}jeunes? entreprises? [a-z' -]{3,60}"]
AUTRE_JE = "Autre statut JE"

ORDRE_TAGS = ("CIR", "CII", "CIC", "JEI", "JEIR", "JEC", "JEU", "JEII", AUTRE_JE)

# Rapprochement des versions d'un même amendement (commission, séance, lectures suivantes)
SEUIL_MEME_ARTICLE = 0.85    # similarité minimale des dispositifs visant le même article
SEUIL_AUTRE_ARTICLE = 0.95   # similarité minimale si l'article visé a changé
LONGUEUR_MIN_AUTRE_ARTICLE = 300
ORDRE_INSTANCE = {"Commission des finances": 0, "Commission des affaires sociales": 0,
                  "Commission saisie pour avis": 0, "Séance publique": 1}

# Correspondance entre le sort AN et les options du select Notion.
# L'ordre compte : le premier motif trouvé l'emporte.
SORTS = [
    ("irrecevable", "Irrecevable"),
    ("retir", "Retiré"),
    ("non soutenu", "Non soutenu"),
    ("tomb", "Tombé"),
    ("rejet", "Rejeté"),
    ("adopt", "Adopté"),
]

URL_AMENDEMENT = "https://www.assemblee-nationale.fr/dyn/17/amendements/{uid}"

# ---------------------------------------------------------------------------
# OUTILS
# ---------------------------------------------------------------------------


def lire(d, *chemin):
    """Lit une valeur imbriquée sans planter si une clé manque."""
    for cle in chemin:
        if not isinstance(d, dict):
            return None
        d = d.get(cle)
    # L'open data AN code les valeurs vides sous la forme {"@xsi:nil": "true"}
    if isinstance(d, dict) and "@xsi:nil" in d:
        return None
    return d


def chaine(v):
    return v.strip() if isinstance(v, str) else ""


def normaliser(txt):
    txt = unicodedata.normalize("NFKD", txt or "")
    txt = "".join(c for c in txt if not unicodedata.combining(c))
    txt = txt.replace("\u2019", "'").replace("\u2018", "'").replace("`", "'")
    txt = re.sub(r"[\u2010\u2011\u2012\u2013\u2014\u2212]", "-", txt)  # tirets typographiques -> "-"
    txt = re.sub(r"\s+", " ", txt)
    return txt.lower()


def sans_accents(txt):
    """Comme normaliser(), mais en conservant les majuscules (pour les sigles)."""
    txt = unicodedata.normalize("NFKD", txt or "")
    txt = "".join(c for c in txt if not unicodedata.combining(c))
    txt = txt.replace("\u2019", "'").replace("\u2018", "'").replace("`", "'")
    txt = re.sub(r"[\u2010\u2011\u2012\u2013\u2014\u2212]", "-", txt)  # tirets typographiques -> "-"
    return re.sub(r"\s+", " ", txt)


def html_vers_texte(h):
    if not isinstance(h, str) or not h:
        return ""
    h = re.sub(r"(?i)<br\s*/?>|</p>|</li>", "\n", h)
    h = re.sub(r"<[^>]+>", "", h)
    t = html.unescape(h)
    t = re.sub(r"[ \t\u00a0\u202f]+", " ", t)
    t = re.sub(r"\n\s*\n+", "\n\n", t)
    return t.strip()


def decouper(t, n=TAILLE_BLOC):
    """Découpe un texte long en blocs compatibles avec l'API Notion."""
    blocs = []
    while len(t) > n:
        coupe = t.rfind("\n", 0, n)
        if coupe < n // 2:
            coupe = t.rfind(" ", 0, n)
        if coupe <= 0:
            coupe = n
        blocs.append(t[:coupe].strip())
        t = t[coupe:].strip()
    if t:
        blocs.append(t)
    return blocs


def blocs_notion(titre, morceaux):
    """Construit un intertitre suivi de paragraphes au format de l'API Notion."""
    def texte(t):
        return [{"type": "text", "text": {"content": t}}]
    blocs = [{"object": "block", "type": "heading_3", "heading_3": {"rich_text": texte(titre)}}]
    for m in morceaux:
        blocs.append({"object": "block", "type": "paragraph", "paragraph": {"rich_text": texte(m)}})
    return blocs


# Identifiants des propriétés Notion de la base "Veille amendements PLF 2027".
# On utilise les identifiants et non les noms : renommer une colonne dans Notion
# ne casse donc plus la synchronisation. (Nom actuel indiqué en commentaire.)
P = {
    "titre": "title",       # Titre
    "uid": "cKIo",          # UID AN
    "numero": "V|zK",       # N° amendement
    "instance": "LYp=",     # Instance
    "article": "<>Iq",      # Article visé
    "auteurs": "_\\gF",     # Auteur(s)
    "groupe": "q}iE",       # Groupe
    "dispositifs": "vmP_",  # Dispositifs détectés
    "portee": "Dht]",       # Portée
    "sort": "rZHo",         # Sort
    "date_depot": "iPRZ",   # Date de dépôt
    # "Dernière synchro" (AXfC) n'est plus alimentée : la date figure en tête de base
    "lien": "kP^I",         # Lien vers l'amendement
    "fil": "?agS",          # Fil de suivi
    "parcours": "}MM@",     # Parcours
    "texte": "kLqF",        # Texte (PLF 2027 / PLFSS 2027)
}


def proprietes_notion(f, aujourd_hui):
    """Propriétés de la page Notion au format API (chaîne JSON injectée telle quelle par Make).
    Les champs saisis à la main (Analyse Talweg, Catégories, Pertinence) ne sont jamais envoyés."""
    def texte(t):
        return {"rich_text": [{"text": {"content": (t or "")[:1900]}}]}
    p = {
        P["titre"]: {"title": [{"text": {"content": f["titre"][:1900]}}]},
        P["uid"]: texte(f["uid"]),
        P["numero"]: texte(f["numero"]),
        P["instance"]: {"select": {"name": f["instance"]}},
        P["article"]: texte(f["article"]),
        P["auteurs"]: texte(f["auteurs"]),
        P["dispositifs"]: {"multi_select": [{"name": t} for t in f["dispositifs"]]},
        P["portee"]: {"select": {"name": f["portee"]}},
        P["sort"]: {"select": {"name": f["sort"]}},
        P["lien"]: {"url": f["lien"]},
        P["fil"]: texte(f["fil"]),
        P["parcours"]: texte(f["parcours"]),
        P["texte"]: {"select": {"name": f["texte"]}},
    }
    if f["groupe"]:
        p[P["groupe"]] = {"select": {"name": f["groupe"]}}
    if f["date_depot"]:
        p[P["date_depot"]] = {"date": {"start": f["date_depot"]}}
    return json.dumps(p, ensure_ascii=False)


def statuts_inconnus(norm, casse):
    """Repère un éventuel nouveau statut « jeune entreprise » non encore référencé."""
    trouves = set()
    for sigle in re.findall(SIGLE_JE, casse):
        if sigle not in SIGLES_CONNUS and sigle not in MOTS_MAJUSCULES_IGNORES:
            trouves.add(sigle)
    for motif in FORMULES_NOUVEAU_STATUT:
        for m in re.finditer(motif, norm):
            expression = m.group(0)
            if not any(re.search(p, expression) for motifs in MOTS_JEI.values() for p in motifs):
                trouves.add(expression.strip())
    return sorted(trouves)


def detecter(texte, conf):
    """Renvoie les dispositifs cités, selon le périmètre du texte suivi.
    Les références d'articles servent à repérer l'amendement mais ne sont pas affichées :
    article 244 quater B seul -> CIR ; article 44 sexies-0 A ou loi n° 2003-1311 seuls -> JEI."""
    norm, casse = normaliser(texte), sans_accents(texte)
    tags = set()
    if conf["credits_244"]:
        tags |= {t for t, motifs in MOTS_CREDITS.items() if any(re.search(m, norm) for m in motifs)}
        if any(re.search(m, norm) for m in REF_244) and not tags & {"CIR", "CII", "CIC"}:
            tags.add("CIR")
    if conf["jei"]:
        jei = {t for t, motifs in MOTS_JEI.items() if any(re.search(m, norm) for m in motifs)}
        jei |= {t for t, motifs in SIGLES_JEI.items() if any(re.search(m, casse) for m in motifs)}
        inconnus = statuts_inconnus(norm, casse)
        if inconnus:
            jei.add(AUTRE_JE)
        if any(re.search(m, norm) for m in REF_JEIR) and not jei:
            jei.add("JEIR")
        if any(re.search(m, norm) for m in REF_JEI) and not jei:
            jei.add("JEI")
        tags |= jei
    return [t for t in ORDRE_TAGS if t in tags]


def statut(a):
    candidats = [
        lire(a, "cycleDeVie", "sort"),
        lire(a, "cycleDeVie", "etatDesTraitements", "sousEtat", "libelle"),
        lire(a, "cycleDeVie", "etatDesTraitements", "etat", "libelle"),
    ]
    for c in candidats:
        n = normaliser(chaine(c))
        for motif, libelle in SORTS:
            if motif in n:
                return libelle
    return "En discussion"


def instance(numero, conf):
    reste = re.sub(r"^I+-", "", numero.upper())  # retire le préfixe de partie (I-, II-)
    code_fond, libelle_fond = conf["commission_fond"]
    if reste.startswith(code_fond):
        return libelle_fond
    if re.match(r"[A-Z]", reste):
        return "Commission saisie pour avis"
    return "Séance publique"


# ---------------------------------------------------------------------------
# TRAITEMENT
# ---------------------------------------------------------------------------


TENTATIVES = 4  # nombre d'essais de téléchargement avant abandon


def telecharger():
    """Télécharge le zip des amendements, avec plusieurs essais :
    le serveur de l'AN coupe parfois la connexion en cours de transfert."""
    chemin = Path(tempfile.gettempdir()) / "amendements_an.zip"
    for essai in range(1, TENTATIVES + 1):
        try:
            print(f"Téléchargement de l'open data AN (essai {essai}/{TENTATIVES})...")
            with requests.get(URL_ZIP, stream=True, timeout=900) as r:
                r.raise_for_status()
                attendu = int(r.headers.get("Content-Length") or 0)
                with open(chemin, "wb") as f:
                    for morceau in r.iter_content(chunk_size=1 << 20):
                        f.write(morceau)
            recu = chemin.stat().st_size
            if attendu and recu != attendu:
                raise IOError(f"fichier incomplet ({recu} octets sur {attendu})")
            if not zipfile.is_zipfile(chemin):
                raise IOError("le fichier reçu n'est pas un zip valide")
            print(f"  {recu / 1e6:.0f} Mo téléchargés")
            return chemin
        except (requests.RequestException, IOError) as e:
            print(f"  Échec : {e}")
            if essai == TENTATIVES:
                raise
            attente = 60 * essai
            print(f"  Nouvel essai dans {attente} s")
            time.sleep(attente)


# Référentiels des groupes politiques (remplis par charger_groupes)
GROUPES = {}        # PO... -> "EPR - Ensemble pour la République"
GROUPE_DEPUTE = {}  # PA... -> PO... du groupe actuel du député
NOMS = {}           # PA... -> "M. Paul Midy"


def charger_groupes():
    """Charge les groupes politiques depuis l'open data AN (députés en exercice).
    En cas d'échec, le script continue : la propriété Groupe reste simplement vide."""
    try:
        print("Téléchargement du référentiel des groupes politiques...")
        chemin = Path(tempfile.gettempdir()) / "deputes_an.zip"
        r = requests.get(URL_DEPUTES, timeout=300)
        r.raise_for_status()
        chemin.write_bytes(r.content)
        with zipfile.ZipFile(chemin) as zf:
            for nom in zf.namelist():
                if not nom.endswith(".json"):
                    continue
                with zf.open(nom) as f:
                    brut = json.load(f)
                if "organe" in brut:
                    o = brut["organe"]
                    if chaine(lire(o, "codeType")) == "GP":
                        sigle = chaine(lire(o, "libelleAbrev")) or chaine(lire(o, "libelleAbrege"))
                        nom_long = chaine(lire(o, "libelle"))
                        if sigle and nom_long and nom_long != sigle:
                            etiquette = f"{sigle} - {nom_long}"
                        else:
                            etiquette = sigle or nom_long
                        # Notion interdit les virgules dans une option de sélection (100 caractères max)
                        GROUPES[chaine(lire(o, "uid"))] = re.sub(r"\s*,\s*", " ", etiquette)[:100]
                elif "acteur" in brut:
                    act = brut["acteur"]
                    uid = lire(act, "uid")
                    uid = chaine(uid.get("#text")) if isinstance(uid, dict) else chaine(uid)
                    ident = lire(act, "etatCivil", "ident") or {}
                    nom = " ".join(x for x in (chaine(lire(ident, "civ")), chaine(lire(ident, "prenom")),
                                               chaine(lire(ident, "nom"))) if x)
                    if nom:
                        NOMS[uid] = nom
                    mandats = lire(act, "mandats", "mandat") or []
                    if isinstance(mandats, dict):
                        mandats = [mandats]
                    for m in mandats:
                        if chaine(lire(m, "typeOrgane")) == "GP" and not lire(m, "dateFin"):
                            GROUPE_DEPUTE[uid] = chaine(lire(m, "organes", "organeRef"))
        print(f"  {len(GROUPES)} groupes, {len(GROUPE_DEPUTE)} députés rattachés")
    except Exception as e:  # le référentiel est un bonus, jamais bloquant
        print(f"  Référentiel des groupes indisponible ({e}) : propriété Groupe laissée vide")


def auteur_principal(a):
    """Premier signataire (porteur de l'amendement), nom complet si disponible."""
    auteur = lire(a, "signataires", "auteur") or {}
    nom = NOMS.get(chaine(lire(auteur, "acteurRef")))
    if nom:
        return nom
    # Repli : premier nom de la liste des signataires ("M. Midy, Mme X et Mme Y" -> "M. Midy")
    liste = html_vers_texte(lire(a, "signataires", "libelle"))
    premier = re.split(r",| et ", liste, maxsplit=1)[0].strip()
    if premier:
        return premier
    if "gouvernement" in normaliser(chaine(lire(auteur, "typeAuteur"))):
        return "Gouvernement"
    return ""


def groupe(a):
    auteur = lire(a, "signataires", "auteur") or {}
    type_auteur = normaliser(chaine(lire(auteur, "typeAuteur")))
    ref = chaine(lire(auteur, "groupePolitiqueRef")) or GROUPE_DEPUTE.get(chaine(lire(auteur, "acteurRef")), "")
    if ref in GROUPES:
        return GROUPES[ref]
    if "gouvernement" in type_auteur:
        return "Gouvernement"
    if "rapporteur" in type_auteur or "commission" in type_auteur:
        return "Commission"
    return None


def extraire(a, conf):
    """Transforme un amendement brut AN en fiche prête pour Notion."""
    uid = chaine(lire(a, "uid"))
    numero = chaine(lire(a, "identification", "numeroLong"))
    article = (chaine(lire(a, "pointeurFragmentTexte", "division", "articleDesignationCourte"))
               or chaine(lire(a, "pointeurFragmentTexte", "division", "titre")))
    dispositif = html_vers_texte(lire(a, "corps", "contenuAuteur", "dispositif"))
    expose = html_vers_texte(lire(a, "corps", "contenuAuteur", "exposeSommaire"))
    auteurs = auteur_principal(a)
    date_depot = chaine(lire(a, "cycleDeVie", "dateDepot"))[:10]

    tags_dispositif = detecter(" ".join([article, dispositif]), conf)
    tags = detecter(" ".join([article, dispositif, expose]), conf)
    if not tags:
        return None
    portee = "Dispositif" if tags_dispositif else "Exposé seul"
    inconnus = statuts_inconnus(normaliser(dispositif + " " + expose), sans_accents(dispositif + " " + expose)) \
        if conf["jei"] else []
    dispositif_blocs = decouper(dispositif)
    expose_blocs = decouper(expose)

    return {
        "uid": uid,
        "texte": conf["libelle"],
        "titre": (conf["prefixe_titre"] + f"{numero} · {article}").strip(" ·"),
        "numero": numero,
        "instance": instance(numero, conf),
        "article": article,
        "auteurs": auteurs[:1900],
        "groupe": groupe(a),
        "dispositifs": tags,
        "portee": portee,
        "sort": statut(a),
        "date_depot": date_depot or None,
        "lien": URL_AMENDEMENT.format(uid=uid),
        "dispositif_blocs": dispositif_blocs,
        "expose_blocs": expose_blocs,
        # Corps de page Notion prêt à l'emploi (chaîne JSON injectée telle quelle par Make)
        "statuts_inconnus": inconnus,
        "blocs_notion": json.dumps(
            (blocs_notion("Statut « jeune entreprise » non référencé détecté", ["; ".join(inconnus)])
             if inconnus else [])
            + blocs_notion("Dispositif", dispositif_blocs)
            + blocs_notion("Exposé sommaire", expose_blocs),
            ensure_ascii=False),
    }


def cle_texte(fiche):
    """Texte du dispositif réduit à l'essentiel pour comparer deux versions :
    sans gage financier, sans numérotation, sans ponctuation ni accents."""
    lignes = "\n".join(fiche["dispositif_blocs"]).split("\n")
    gage = ("perte de recettes", "due concurrence", "accise sur les tabacs", "taxe additionnelle")
    garde = [l for l in lignes if not any(g in normaliser(l) for g in gage)]
    t = normaliser(" ".join(garde))
    t = re.sub(r"\b[ivx]+\s*\.\s*[-\u2013]", " ", t)  # I. -, II. -
    t = re.sub(r"\b\d+\s*°", " ", t)                    # 1°, 2°
    t = re.sub(r"[^a-z0-9 ]", " ", t)
    return re.sub(r"\s+", " ", t).strip()


def rattacher_versions(fiches):
    """Regroupe les versions d'un même amendement (même texte, numéros différents)
    et renseigne pour chacune le fil de suivi et le parcours."""
    cles = [cle_texte(f) for f in fiches]
    articles = [normaliser(f["article"]) for f in fiches]
    parent = list(range(len(fiches)))

    def racine(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for i in range(len(fiches)):
        for j in range(i + 1, len(fiches)):
            a, b = cles[i], cles[j]
            if not a or not b:
                continue
            if articles[i] == articles[j]:
                seuil = SEUIL_MEME_ARTICLE
            elif min(len(a), len(b)) >= LONGUEUR_MIN_AUTRE_ARTICLE:
                seuil = SEUIL_AUTRE_ARTICLE
            else:
                continue
            m = difflib.SequenceMatcher(None, a, b, autojunk=False)
            if m.real_quick_ratio() >= seuil and m.quick_ratio() >= seuil and m.ratio() >= seuil:
                parent[racine(i)] = racine(j)

    familles = {}
    for i in range(len(fiches)):
        familles.setdefault(racine(i), []).append(fiches[i])
    for membres in familles.values():
        membres.sort(key=lambda f: (f["date_depot"] or "", ORDRE_INSTANCE.get(f["instance"], 9), f["numero"]))
        fil = membres[0]["numero"]
        # Parcours par étape : "Commission : I-CF423 (Rejeté) → Séance : I-2734 (En discussion)"
        etapes = []
        for f in membres:
            etape = "Séance" if f["instance"] == "Séance publique" else "Commission"
            if not etapes or etapes[-1][0] != etape:
                etapes.append((etape, []))
            etapes[-1][1].append(f"{f['numero']} ({f['sort']})")
        parcours = " → ".join(f"{e} : {', '.join(n)}" for e, n in etapes)
        for f in membres:
            f["fil"] = fil
            f["parcours"] = parcours if len(membres) > 1 else ""
    return len([m for m in familles.values() if len(m) > 1])


def empreinte(fiche):
    cles = ("numero", "sort", "article", "dispositif_blocs", "expose_blocs", "auteurs", "groupe",
            "dispositifs", "fil", "parcours", "texte", "titre", "instance")
    brut = json.dumps({k: fiche[k] for k in cles}, ensure_ascii=False, sort_keys=True)
    return hashlib.md5(brut.encode("utf-8")).hexdigest()


def main():
    chemin_zip = Path(sys.argv[1]) if len(sys.argv) > 1 else telecharger()
    if len(sys.argv) <= 1:
        charger_groupes()
    aujourd_hui = dt.date.today().isoformat()

    # Base précédente : sert à repérer ce qui est nouveau ou a changé
    precedent = {}
    if FICHIER_BASE.exists():
        for f in json.loads(FICHIER_BASE.read_text(encoding="utf-8"))["amendements"]:
            precedent[f["uid"]] = f

    fiches = []
    nb_par_texte = {c["libelle"]: 0 for c in TEXTES}
    with zipfile.ZipFile(chemin_zip) as zf:
        noms = [n for n in zf.namelist() if n.endswith(".json")]
        # Filtre rapide sur le nom de fichier (l'UID contient par exemple "B3210P")
        cibles = [n for n in noms if any(f"B{c['num']}P" in n for c in TEXTES)]
        if not cibles:
            print("  Aucun fichier repéré par son nom, lecture complète (plus lent)...")
            cibles = noms

        for nom in cibles:
            with zf.open(nom) as f:
                try:
                    brut = json.load(f)
                except json.JSONDecodeError:
                    continue
            a = brut.get("amendement", brut)
            ref = chaine(lire(a, "texteLegislatifRef"))
            conf = next((c for c in TEXTES if ref.endswith(f"B{c['num']}")), None)
            if not conf:
                continue
            nb_par_texte[conf["libelle"]] += 1
            fiche = extraire(a, conf)
            if fiche:
                fiches.append(fiche)

    # Rapprochement des versions, texte par texte (jamais entre PLF et PLFSS)
    nb_fils = sum(rattacher_versions([f for f in fiches if f["texte"] == c["libelle"]]) for c in TEXTES)
    for fiche in fiches:
        fiche["notion_proprietes"] = proprietes_notion(fiche, aujourd_hui)
        fiche["empreinte"] = empreinte(fiche)
        ancien = precedent.get(fiche["uid"])
        if ancien and ancien.get("empreinte") == fiche["empreinte"]:
            fiche["derniere_modif"] = ancien["derniere_modif"]
        else:
            fiche["derniere_modif"] = aujourd_hui

    fiches.sort(key=lambda f: (f["date_depot"] or "", f["numero"]))
    limite = (dt.date.today() - dt.timedelta(days=JOURS_DELTA)).isoformat()
    delta = [f for f in fiches if f["derniere_modif"] >= limite]

    DOSSIER.mkdir(exist_ok=True)
    horodatage = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    for chemin, liste in ((FICHIER_BASE, fiches), (FICHIER_DELTA, delta)):
        chemin.write_text(json.dumps(
            {"genere_le": horodatage, "textes": [c["libelle"] for c in TEXTES],
             "nb": len(liste), "amendements": liste},
            ensure_ascii=False, indent=1), encoding="utf-8")

    for c in TEXTES:
        retenus = [f for f in fiches if f["texte"] == c["libelle"]]
        print(f"{c['libelle']} (n° {c['num']}) : {nb_par_texte[c['libelle']]} amendements, "
              f"{len(retenus)} retenus")
        for tag in ORDRE_TAGS:
            n = sum(tag in f["dispositifs"] for f in retenus)
            if n:
                print(f"  {tag} : {n}")
    print(f"Dans le delta : {len(delta)} | amendements présents en plusieurs versions : {nb_fils}")
    for f in fiches:
        if f.get("statuts_inconnus"):
            print(f"  ⚠ Statut JE non référencé dans {f['texte']} {f['numero']} : {', '.join(f['statuts_inconnus'])}")


if __name__ == "__main__":
    main()
