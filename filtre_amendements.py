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
import hashlib
import html
import json
import re
import sys
import tempfile
import unicodedata
import zipfile
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# PARAMÈTRES (les seules lignes à modifier en temps normal)
# ---------------------------------------------------------------------------

URL_ZIP = ("https://data.assemblee-nationale.fr/static/openData/repository/"
           "17/loi/amendements_div_legis/Amendements.json.zip")
NUM_TEXTE = "3210"   # PLF 2027
JOURS_DELTA = 3      # le delta couvre les modifications des 3 derniers jours
TAILLE_BLOC = 1900   # limite Notion : 2000 caractères par bloc de texte

DOSSIER = Path("data")
FICHIER_BASE = DOSSIER / "amendements_plf2027.json"
FICHIER_DELTA = DOSSIER / "delta.json"

# Expressions recherchées, APRÈS normalisation du texte :
# minuscules, sans accents, apostrophes droites, espaces simples.
MOTS_CLES = {
    "CIR": [r"credits? d'impot (en faveur de la )?recherche", r"\bcir\b"],
    "CII": [r"credits? d'impot (en faveur de l')?innovation", r"\bcii\b"],
    "Collection": [r"credits? d'impot collection", r"nouvelles collections"],
    "JEI": [r"jeunes? entreprises? innovantes?", r"\bjei\b",
            r"jeunes? entreprises? d'innovation de rupture",
            r"jeunes? entreprises? de croissance", r"44 sexies-0 a"],
    "Art. 244 quater B": [r"244 quater b"],
}

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


def detecter(texte_normalise):
    return [tag for tag, motifs in MOTS_CLES.items()
            if any(re.search(m, texte_normalise) for m in motifs)]


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


def telecharger():
    print("Téléchargement de l'open data AN...")
    chemin = Path(tempfile.gettempdir()) / "amendements_an.zip"
    with requests.get(URL_ZIP, stream=True, timeout=900) as r:
        r.raise_for_status()
        with open(chemin, "wb") as f:
            for morceau in r.iter_content(chunk_size=1 << 20):
                f.write(morceau)
    print(f"  {chemin.stat().st_size / 1e6:.0f} Mo téléchargés")
    return chemin


def extraire(a):
    """Transforme un amendement brut AN en fiche prête pour Notion."""
    uid = chaine(lire(a, "uid"))
    numero = chaine(lire(a, "identification", "numeroLong"))
    article = (chaine(lire(a, "pointeurFragmentTexte", "division", "articleDesignationCourte"))
               or chaine(lire(a, "pointeurFragmentTexte", "division", "titre")))
    dispositif = html_vers_texte(lire(a, "corps", "contenuAuteur", "dispositif"))
    expose = html_vers_texte(lire(a, "corps", "contenuAuteur", "exposeSommaire"))
    auteurs = html_vers_texte(lire(a, "signataires", "libelle"))
    date_depot = chaine(lire(a, "cycleDeVie", "dateDepot"))[:10]

    tags = detecter(normaliser(" ".join([article, dispositif, expose])))
    if not tags:
        return None

    return {
        "uid": uid,
        "titre": f"{numero} · {article}".strip(" ·"),
        "numero": numero,
        "instance": instance(numero),
        "article": article,
        "auteurs": auteurs[:1900],
        "dispositifs": tags,
        "sort": statut(a),
        "date_depot": date_depot or None,
        "lien": URL_AMENDEMENT.format(uid=uid),
        "dispositif_blocs": decouper(dispositif),
        "expose_blocs": decouper(expose),
    }


def empreinte(fiche):
    cles = ("numero", "sort", "article", "dispositif_blocs", "expose_blocs", "auteurs")
    brut = json.dumps({k: fiche[k] for k in cles}, ensure_ascii=False, sort_keys=True)
    return hashlib.md5(brut.encode("utf-8")).hexdigest()


def main():
    chemin_zip = Path(sys.argv[1]) if len(sys.argv) > 1 else telecharger()
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
            if not fiche:
                continue
            fiche["empreinte"] = empreinte(fiche)
            ancien = precedent.get(fiche["uid"])
            if ancien and ancien.get("empreinte") == fiche["empreinte"]:
                fiche["derniere_modif"] = ancien["derniere_modif"]
            else:
                fiche["derniere_modif"] = aujourd_hui
            fiches.append(fiche)

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
    for tag in MOTS_CLES:
        print(f"  {tag} : {sum(tag in f['dispositifs'] for f in fiches)}")


if __name__ == "__main__":
    main()
