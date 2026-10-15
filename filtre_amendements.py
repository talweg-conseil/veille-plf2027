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
NUM_TEXTE = "3210"   # PLF 2027
JOURS_DELTA = 0      # le delta ne contient que les changements du jour (0 = aujourd'hui seulement)
TAILLE_BLOC = 1900   # limite Notion : 2000 caractères par bloc de texte

DOSSIER = Path("data")
FICHIER_BASE = DOSSIER / "amendements_plf2027.json"
FICHIER_DELTA = DOSSIER / "delta.json"

# Expressions recherchées, APRÈS normalisation du texte :
# minuscules, sans accents, apostrophes droites, espaces simples.
MOTS_CLES = {
    "CIR": [r"credits? d'impot (en faveur de la )?recherche", r"\bcir\b", r"199 ter b"],
    "CII": [r"credits? d'impot (en faveur de l')?innovation", r"\bcii\b"],
    "CIC": [r"credits? d'impot collection", r"nouvelles collections"],
    "JEI": [r"jeunes? entreprises? innovantes?", r"\bjei\b",
            r"jeunes? entreprises? d'innovation de rupture",
            r"jeunes? entreprises? de croissance", r"44 sexies-0 a"],
    "Art. 244 quater B": [r"244 quater b"],  # sert à la recherche, jamais affiché
}

# Étiquettes affichées dans Notion (colonne Dispositif(s))
CREDITS_244 = ("CIR", "CII", "CIC")   # crédits d'impôt de l'article 244 quater B
ART_244 = "Art. 244 quater B"

# Rapprochement des versions d'un même amendement (commission, séance, lectures suivantes)
SEUIL_MEME_ARTICLE = 0.85    # similarité minimale des dispositifs visant le même article
SEUIL_AUTRE_ARTICLE = 0.95   # similarité minimale si l'article visé a changé
LONGUEUR_MIN_AUTRE_ARTICLE = 300
ORDRE_INSTANCE = {"Commission des finances": 0, "Commission saisie pour avis": 0, "Séance publique": 1}

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
    txt = re.sub(r"\s+", " ", txt)
    return txt.lower()


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
    }
    if f["groupe"]:
        p[P["groupe"]] = {"select": {"name": f["groupe"]}}
    if f["date_depot"]:
        p[P["date_depot"]] = {"date": {"start": f["date_depot"]}}
    return json.dumps(p, ensure_ascii=False)


def detecter(texte_normalise):
    """Renvoie les dispositifs cités parmi CIR, CII, CIC et JEI.
    L'article 244 quater B sert à repérer l'amendement mais n'est pas affiché :
    s'il est cité sans que le crédit d'impôt soit nommé, on retient CIR par défaut."""
    tags = [tag for tag, motifs in MOTS_CLES.items()
            if any(re.search(m, texte_normalise) for m in motifs)]
    if ART_244 in tags:
        tags.remove(ART_244)
        if not any(t in tags for t in CREDITS_244):
            tags.insert(0, "CIR")
    return tags


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


def instance(numero):
    reste = re.sub(r"^I+-", "", numero.upper())  # retire le préfixe de partie (I-, II-)
    if reste.startswith("CF"):
        return "Commission des finances"
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


def extraire(a):
    """Transforme un amendement brut AN en fiche prête pour Notion."""
    uid = chaine(lire(a, "uid"))
    numero = chaine(lire(a, "identification", "numeroLong"))
    article = (chaine(lire(a, "pointeurFragmentTexte", "division", "articleDesignationCourte"))
               or chaine(lire(a, "pointeurFragmentTexte", "division", "titre")))
    dispositif = html_vers_texte(lire(a, "corps", "contenuAuteur", "dispositif"))
    expose = html_vers_texte(lire(a, "corps", "contenuAuteur", "exposeSommaire"))
    auteurs = auteur_principal(a)
    date_depot = chaine(lire(a, "cycleDeVie", "dateDepot"))[:10]

    tags_dispositif = detecter(normaliser(" ".join([article, dispositif])))
    tags = detecter(normaliser(" ".join([article, dispositif, expose])))
    if not tags:
        return None
    portee = "Dispositif" if tags_dispositif else "Exposé seul"
    dispositif_blocs = decouper(dispositif)
    expose_blocs = decouper(expose)

    return {
        "uid": uid,
        "titre": f"{numero} · {article}".strip(" ·"),
        "numero": numero,
        "instance": instance(numero),
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
        "blocs_notion": json.dumps(
            blocs_notion("Dispositif", dispositif_blocs)
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
            "dispositifs", "fil", "parcours")
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

    fiches, nb_texte = [], 0
    with zipfile.ZipFile(chemin_zip) as zf:
        noms = [n for n in zf.namelist() if n.endswith(".json")]
        # Filtre rapide sur le nom de fichier (l'UID contient "B3210P")
        cibles = [n for n in noms if f"B{NUM_TEXTE}P" in n]
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
            if not chaine(lire(a, "texteLegislatifRef")).endswith(f"B{NUM_TEXTE}"):
                continue
            nb_texte += 1
            fiche = extraire(a)
            if fiche:
                fiches.append(fiche)

    nb_fils = rattacher_versions(fiches)
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
            {"genere_le": horodatage, "texte": NUM_TEXTE, "nb": len(liste), "amendements": liste},
            ensure_ascii=False, indent=1), encoding="utf-8")

    print(f"Amendements sur le texte {NUM_TEXTE} : {nb_texte}")
    print(f"Retenus (mots-clés) : {len(fiches)} | dans le delta : {len(delta)}")
    print(f"Amendements présents en plusieurs versions : {nb_fils}")
    for tag in ("CIR", "CII", "CIC", "JEI"):
        print(f"  {tag} : {sum(tag in f['dispositifs'] for f in fiches)}")


if __name__ == "__main__":
    main()
