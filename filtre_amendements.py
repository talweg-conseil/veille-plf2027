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