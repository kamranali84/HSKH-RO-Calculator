"""
HSKH RO Calculator
Multi-vendor RO design (1-4 passes): feed analysis, membrane selection with flux / flow cautions, pass & stage design,
all pre- / inter- / post-treatment chemicals, pressure & power, treated-water quality and a PDF report.

Run:  streamlit run hskh_ro_calculator.py

Membrane library: your original 13 membranes plus 66 DuPont FilmTec / Nitto Hydranautics / LG Chem models from the manufacturers'
published datasheets (area, salt rejection, standard-test flow).  Permeability (A_w) of the added models is scaled from the datasheet
test flow to the ESPA2 MAX calibration (IMSDesign run); element pressure drop is the generic calibration value - replace them with
datasheet / projection-software values on the Library page before using pressures for design.
"""
import hashlib
import json
import math
import re
from contextlib import contextmanager
from datetime import datetime
from html import escape as hesc
from io import BytesIO
from math import exp, log, log10
from pathlib import Path
from xml.sax.saxutils import escape

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.platypus import KeepTogether, PageBreak, Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle

APP_TITLE = "HSKH RO Calculator"
st.set_page_config(page_title=APP_TITLE, page_icon="💧", layout="wide", initial_sidebar_state="expanded")
ss = st.session_state

# =====================================================
# SETTINGS
# =====================================================
THEME = "sky blue"                    # "sky blue" (bluish gradient, white boxes / tabs, black text), "metal blue", "light blue", "grey", "grey green", "light brown" or "charcoal"
APP_WIDTH_VW = 60
PROJECT_DIR = Path(__file__).resolve().parent / "HSKH_RO_Projects"
PROJECT_EXT = ".ro"
LIB_FILE = PROJECT_DIR / "membrane_library.json"
AUTOLOAD_LAST = True
NO_SAVE_PREFIX = ("_", "ui_", "FormSubmitter", "nav", "w_")
MAIN_TABS = ["📁 Projects", "💧 Feed Water", "📈 RO Design", "🧪 Chemicals", "🌊 Hydraulics & Power",
             "✅ Water Quality", "📄 Report", "📚 Library"]
WATER_TYPES = ["RO/NF Permeate", "Softened Water", "Well Water", "Ground Water", "Municipal Water",
               "Surface Water", "Brackish Water", "Sea Water"]

# >>> PURE-START  (no Streamlit calls below this line until PURE-END; tested on its own)
# =====================================================
# CONSTANTS
# =====================================================
GPM = 4.40287             # m3/h -> gpm
PSI = 14.5038             # bar -> psi
HP_KW = 0.7457
R_BAR = 0.08314           # L.bar/(mol.K)
CO2_PASSAGE = 0.88        # fraction of feed CO2 that passes the membrane (calibrated: reproduces the IMSDesign NaOH dose)
SILICA_SP_FACTOR = 4.0    # silica passage = salt passage x 4
SP_DILUTE_FACTOR = 2.3    # salt passage multiplier for dilute feed (TDS < SP_DILUTE_TDS): calibrated to the IMSDesign product TDS / HCO3
SP_DILUTE_TDS = 500.0
DP_EXPONENT = 1.7         # element pressure drop ~ flow^1.7
REC_PER_ELEMENT = {1: 0.10, 2: 0.15}   # recovery per element in series: pass 1 raw water, pass 2 clean RO-permeate feed

# key, label, molar mass g/mol, charge, equivalent conductance S.cm2/eq
CATIONS = [("ca", "Ca", 40.078, 2, 59.5), ("mg", "Mg", 24.305, 2, 53.1), ("na", "Na", 22.990, 1, 50.1),
           ("k", "K", 39.098, 1, 73.5), ("nh4", "NH4", 18.039, 1, 73.5), ("ba", "Ba", 137.327, 2, 63.6),
           ("sr", "Sr", 87.620, 2, 59.4), ("fe", "Fe", 55.845, 2, 54.0), ("mn", "Mn", 54.938, 2, 53.5)]
ANIONS = [("hco3", "HCO3", 61.017, 1, 44.5), ("co3", "CO3", 60.009, 2, 69.3), ("so4", "SO4", 96.060, 2, 80.0),
          ("cl", "Cl", 35.453, 1, 76.3), ("f", "F", 18.998, 1, 54.4), ("no3", "NO3", 62.005, 1, 71.4),
          ("po4", "PO4", 94.971, 3, 69.0), ("br", "Br", 79.904, 1, 78.1)]
ION_KEYS = [r[0] for r in CATIONS + ANIONS]
ION_LABEL = {r[0]: r[1] for r in CATIONS + ANIONS}
ION_MW = {r[0]: r[2] for r in CATIONS + ANIONS}
ION_Z = {r[0]: r[3] for r in CATIONS + ANIONS}
ION_LAM = {r[0]: r[4] for r in CATIONS + ANIONS}

SDI_REQ = {"RO/NF Permeate": "SDI < 1", "Softened Water": "SDI < 3", "Well Water": "SDI < 3", "Ground Water": "SDI < 3",
           "Municipal Water": "SDI < 5", "Surface Water": "SDI < 5", "Brackish Water": "Membrane pretreatment, SDI < 3",
           "Sea Water": "Conventional pretreatment + UF, SDI < 3"}
# recommended maximum average flux (gfd): pass 1, pass 2  (from your original code)
FLUX_DEFAULT = {"RO/NF Permeate": [16.0, 18.0], "Softened Water": [15.0, 16.0], "Ground Water": [12.0, 15.0],
                "Well Water": [12.0, 15.0], "Municipal Water": [13.0, 16.0], "Surface Water": [10.0, 12.0],
                "Brackish Water": [12.0, 15.0], "Sea Water": [8.0, 10.0]}

# calibration of the type-typical permeability and element pressure drop (see calibrate in the tests)
AW_BY_TYPE = {"Low Energy BWRO": 0.1728, "Ultra Low Energy BWRO": 0.26, "Sanitary BWRO": 0.125, "Nanofiltration": 0.29, "High Pressure RO": 0.045, "BWRO": 0.128, "High Rejection BWRO": 0.112,
              "Fouling Resistant BWRO": 0.118, "SWRO": 0.044}   # gfd/psi at 25 C (new membrane); Low Energy = IMSDesign calibration
DP_REF_DEFAULT = 1.27          # psi per element at 50 gpm (IMSDesign calibration)
MAXP_BY_TYPE = {"SWRO": 1200.0}
MAXP_DEFAULT = 600.0           # psi

IMS_EXAMPLE = {
    "project_name": "NTPC11 (IMSDesign example)", "ca": 8.82, "mg": 4.41, "na": 15.5, "k": 3.24, "ba": 0.08, "sr": 0.05,
    "hco3": 48.8, "co3": 0.003, "so4": 13.84, "cl": 12.57, "f": 0.19, "no3": 5.72, "sio2": 11.8, "ph": 6.0,
    "temp_c": 28.8, "water_type": "Brackish Water", "passes": 2, "product_flow": 209.95 / GPM, "flow_unit": "m³/h",
    "p1_rec": 85.0, "p2_rec": 85.0, "recycle": True, "age1": 3.0, "decl1": 7.0, "sp1": 7.0, "age2": 3.0, "decl2": 3.0,
    "sp2": 5.0, "vendor1": "Nitto Hydranautics", "series1": "ESPA", "model1": "ESPA2 MAX", "same2": True,
    "p1_stages": 3, "p1_s1_v": 6, "p1_s1_e": 6, "p1_s2_v": 3, "p1_s2_e": 6, "p1_s3_v": 1, "p1_s3_e": 6,
    "p2_stages": 2, "p2_s1_v": 4, "p2_s1_e": 6, "p2_s2_v": 2, "p2_s2_e": 6, "p1_chem": "None", "p1_ph": 6.0,
    "p2_chem": "NaOH", "p2_ph": 8.2, "as_dose_manual": 3.0, "as_mode": "Manual dose"}
DEF_STAGE = {1: {1: (6, 6), 2: (3, 6), 3: (2, 6)}, 2: {1: (4, 6), 2: (2, 6), 3: (1, 6)},
             3: {1: (4, 6), 2: (2, 6), 3: (1, 6)}, 4: {1: (4, 6), 2: (2, 6), 3: (1, 6)}}
MAX_PASSES = 4


def fmt(v, d=1, unit=""):
    try:
        s = f"{float(v):,.{d}f}"
    except (TypeError, ValueError):
        s = str(v)
    return f"{s} {unit}".strip()


_ASCII = {"³": "3", "²": "2", "µ": "u", "≤": "<=", "≥": ">=", "×": "x", "–": "-", "—": "-", "·": "-", "°": " deg ",
          "₂": "2", "₃": "3", "₄": "4", "→": "->", "⁻": "-", "÷": "/", "≈": "~", "Ω": "ohm"}


def ascii_txt(s):
    s = str(s)
    for a, b in _ASCII.items():
        s = s.replace(a, b)
    return re.sub(r"[^\x20-\x7E]", "", s)


def _f(key, default=0.0):
    try:
        v = ss.get(key, default)
        return float(v) if v is not None else float(default)
    except (TypeError, ValueError):
        return float(default)


# =====================================================
# LIBRARY  (membranes by vendor + vendor guidelines + antiscalants + flux table)
# =====================================================
LEGACY_MEMBRANES = [   # vendor, series, model, area ft2, rejection %, type   (your original database)
    ("DuPont", "FilmTec BW", "BW30-400", 400, 99.5, "BWRO"),
    ("DuPont", "FilmTec BW", "BW30HRLE-440i", 440, 99.7, "Low Energy BWRO"),
    ("DuPont", "FilmTec BW", "BW30XFR-400/34i", 400, 99.7, "Fouling Resistant BWRO"),
    ("DuPont", "FilmTec SW", "SW30HRLE-400", 400, 99.8, "SWRO"),
    ("Nitto Hydranautics", "ESPA", "ESPA2 MAX", 440, 99.6, "Low Energy BWRO"),
    ("LG Chem", "BW", "LG BW 400 R G2", 400, 99.6, "BWRO"),
    ("LG Chem", "BW", "LG BW 440 ES", 440, 99.6, "Low Energy BWRO"),
    ("Toray", "TM800", "TM820M-400", 400, 99.5, "BWRO"),
    ("Toray", "TM800", "TM820M-440", 440, 99.7, "High Rejection BWRO"),
    ("Lanxess", "ACM", "ACM5", 400, 99.6, "BWRO"),
    ("Lanxess", "ACM", "ACM6", 440, 99.7, "High Rejection BWRO"),
]
MEM_DEFAULTS = {"area_ft2": 400.0, "rejection": 99.5, "a_w": 0.125, "dp_ref": DP_REF_DEFAULT, "max_pressure": 600.0, "size_in": 8.0}
MEM_TEXT = ["vendor", "series", "model", "type", "source", "notes"]
MEM_COLUMNS = ["vendor", "series", "model", "type"] + list(MEM_DEFAULTS) + ["source", "notes"]

VENDOR_DEFAULTS = {"tool": "", "max_feed_gpm": 75.0, "min_conc_gpm": 18.0, "max_dp_element": 15.0, "max_dp_vessel": 50.0,
                   "max_lead_rec": 18.0, "max_temp_c": 45.0, "ph_min": 2.0, "ph_max": 11.0, "max_free_cl": 0.1,
                   "max_sdi": 5.0, "flux_scale": 1.0, "note": ""}


def builtin_vendors():
    v = {name: dict(VENDOR_DEFAULTS) for name in ("DuPont", "Nitto Hydranautics", "LG Chem", "Toray", "Lanxess", "Custom")}
    v["DuPont"]["tool"] = "WAVE"
    v["Nitto Hydranautics"]["tool"] = "IMSDesign"
    v["LG Chem"]["tool"] = "LG Q+"
    v["Toray"]["tool"] = "Toray DS2"
    v["Lanxess"]["tool"] = "LewaPlus"
    for name in v:
        v[name]["note"] = "Typical 8-inch element guidelines (75 gpm max feed, 18 gpm min concentrate, 15 psi element dP, 50 psi vessel dP, 18 % lead-element recovery). Replace with the manufacturer's values."
    return v


BUILTIN_VER = 3        # bump when built-in membranes are added: a saved library then receives the missing ones once
# original-database rows that were wrong against the IMSDesign list: an unedited saved copy is replaced by the corrected built-in row
OLD_LEGACY_VALUES = {("Nitto Hydranautics", "ESPA4 MAX"): {"rejection": 99.5, "area_ft2": 440.0},
                     ("Nitto Hydranautics", "CPA5-LD"): {"rejection": 99.8, "area_ft2": 440.0}}


def _aw_test(gpd, area_ft2, psi, ppm, rec):
    """Permeability (gfd/psi) implied by a datasheet standard test: flux / (applied - osmotic (NaCl, log-mean) - 1.5 psi dP)."""
    phi = 0.93 if ppm >= 20000 else 1.0
    pi_f = ppm / 58.44 / 1000 * 2 * phi * R_BAR * 298.15 * PSI       # mg/L -> mol/L, NaCl gives 2 osmoles
    lm = log(1 / (1 - rec)) / rec
    ndp = psi - pi_f * lm - 1.5
    return (gpd / area_ft2) / ndp if ndp > 1 else 0.0


AW_SCALE = 0.1728 / _aw_test(12000, 440, 150, 1500, 0.15)      # anchors every model to the calibrated ESPA2 MAX (IMSDesign run)

# vendor, series, model, area ft2, stabilized salt rejection %, type, datasheet permeate gpd, test psi, test NaCl ppm, test recovery
# Area / rejection / flow from the manufacturers' published datasheets and catalogues (DuPont FilmTec, Hydranautics, LG Chem).
_N = "Nitto Hydranautics"


def _I(spacer, size=8.0, assumed=False):
    """Options of a row taken from the IMSDesign membrane list."""
    return {"src": "IMSDesign membrane list", "spacer": spacer, "size": float(size), "assumed": assumed}


NEW_MEMBRANES = [
    ("DuPont", "FilmTec BW", "BW30 PRO-365", 365, 99.55, "High Rejection BWRO", 10000, 225, 2000, .15),
    ("DuPont", "FilmTec BW", "BW30 PRO-400", 400, 99.60, "High Rejection BWRO", 11000, 225, 2000, .15),
    ("DuPont", "FilmTec BW", "BW30 PRO-400/34", 400, 99.60, "High Rejection BWRO", 11000, 225, 2000, .15),
    ("DuPont", "FilmTec BW", "BW30HR-440", 440, 99.70, "High Rejection BWRO", 12650, 225, 2000, .15),
    ("DuPont", "FilmTec BW", "BW30XHR PRO-400/34", 400, 99.80, "High Rejection BWRO", 11500, 225, 2000, .15),
    ("DuPont", "FilmTec BW", "BW30XHR PRO-440", 440, 99.80, "High Rejection BWRO", 12650, 225, 2000, .15),
    ("DuPont", "FilmTec Low Energy", "BW30HRLE-440", 440, 99.30, "Low Energy BWRO", 12650, 150, 2000, .15),
    ("DuPont", "FilmTec Low Energy", "BW30XFRLE-400/34", 400, 99.30, "Low Energy BWRO", 11500, 150, 2000, .15),
    ("DuPont", "FilmTec Low Energy", "XLE-440", 440, 99.00, "Ultra Low Energy BWRO", 14000, 125, 2000, .15),
    ("DuPont", "FilmTec Low Energy", "SG30LE-440i", 440, 99.50, "Low Energy BWRO", 11500, 225, 2000, .15),
    ("DuPont", "FilmTec Eco", "Eco Pro-400", 400, 99.70, "Low Energy BWRO", 11500, 150, 2000, .15),
    ("DuPont", "FilmTec Eco", "Eco Pro-440", 440, 99.70, "Low Energy BWRO", 12650, 150, 2000, .15),
    ("DuPont", "FilmTec Eco", "Eco Platinum-440", 440, 99.70, "Low Energy BWRO", 12650, 150, 2000, .15),
    ("DuPont", "FilmTec Fortilife", "Fortilife CR50", 400, 99.60, "Fouling Resistant BWRO", 11500, 225, 2000, .15),
    ("DuPont", "FilmTec Fortilife", "Fortilife CR100", 400, 99.80, "Fouling Resistant BWRO", 11500, 225, 2000, .15),
    ("DuPont", "FilmTec Fortilife", "Fortilife CR200", 400, 99.70, "Fouling Resistant BWRO", 12500, 225, 2000, .15),
    ("DuPont", "FilmTec SW", "SW30HRLE-440", 440, 99.80, "SWRO", 8000, 800, 32000, .08),
    ("DuPont", "FilmTec SW", "SW30XLE-400i", 400, 99.80, "SWRO", 9000, 800, 32000, .08),
    ("DuPont", "FilmTec SW", "SW30XLE-440", 440, 99.80, "SWRO", 9900, 800, 32000, .08),
    ("DuPont", "FilmTec SW", "SW30XLE-440i", 440, 99.80, "SWRO", 9900, 800, 32000, .08),
    ("DuPont", "FilmTec SW", "SW30ULE-400i", 400, 99.60, "SWRO", 8400, 700, 32000, .08),
    ("DuPont", "FilmTec SW", "SW30ULE-440i", 440, 99.60, "SWRO", 9000, 700, 32000, .08),
    # ---- Nitto Hydranautics: IMSDesign membrane list (nominal production, rejection, area, spacer, test pressure) ----
    (_N, "ESPA", "ESPA1", 400, 99.4, "Low Energy BWRO", 12000, 150, 1500, .15, _I(31)),
    (_N, "ESPA", "ESPA2-LD", 400, 99.6, "Low Energy BWRO", 10000, 150, 1500, .15, _I(34)),
    (_N, "ESPA", "ESPA2-LD MAX", 440, 99.6, "Low Energy BWRO", 12000, 150, 1500, .15, _I(34)),
    (_N, "ESPA", "ESPA4 MAX", 440, 99.2, "Ultra Low Energy BWRO", 13200, 100, 500, .15, _I(28)),
    (_N, "ESPA", "ESPA4-LD", 400, 99.2, "Ultra Low Energy BWRO", 12000, 100, 500, .15, _I(34)),
    (_N, "ESPA", "ESPA4-LD HP", 400, 99.2, "Ultra Low Energy BWRO", 11000, 100, 500, .15, _I(34)),
    (_N, "ESPA", "ESPAB MAX", 440, 99.3, "Low Energy BWRO", 9000, 150, 1500, .15, {"assumed": True}),
    (_N, "CPA", "CPA2", 365, 99.7, "High Rejection BWRO", 10000, 225, 1500, .15, {}),
    (_N, "CPA", "CPA3", 400, 99.7, "High Rejection BWRO", 11000, 225, 1500, .15, _I(34)),
    (_N, "CPA", "CPA5 MAX", 440, 99.7, "High Rejection BWRO", 12000, 225, 1500, .15, _I(28)),
    (_N, "CPA", "CPA5-LD", 400, 99.7, "High Rejection BWRO", 11000, 225, 1500, .15, _I(34)),
    (_N, "CPA", "CPA6 MAX", 440, 99.8, "High Rejection BWRO", 8000, 225, 1500, .15, _I(28)),
    (_N, "CPA", "CPA6-LD", 400, 99.8, "High Rejection BWRO", 7300, 225, 1500, .15, _I(34)),
    (_N, "CPA", "CPA7 MAX", 440, 99.8, "High Rejection BWRO", 12600, 225, 1500, .15, _I(28)),
    (_N, "CPA", "CPA7-LD", 400, 99.8, "High Rejection BWRO", 11500, 225, 1500, .15, _I(34)),
    (_N, "LFC", "LFC3-LD", 400, 99.7, "Fouling Resistant BWRO", 11000, 225, 1500, .15, _I(34)),
    (_N, "PRO", "PRO-XR1", 400, 99.8, "High Rejection BWRO", 11500, 225, 1500, .15, _I(34, assumed=True)),
    (_N, "PRO", "PRO-LF1", 400, 99.8, "High Pressure RO", 7700, 800, 32000, .08, _I(34, assumed=True)),
    (_N, "SanRO", "SanRO-HS2-8", 380, 99.6, "Sanitary BWRO", 14000, 225, 1500, .15, _I(32, assumed=True)),
    (_N, "SanRO", "SanRO-HS-8", 380, 99.7, "Sanitary BWRO", 10000, 225, 1500, .15, _I(32, assumed=True)),
    (_N, "ESNA", "ESNA1-LF2-LD", 400, 91.0, "Nanofiltration", 12000, 75, 500, .15, _I(34, assumed=True)),
    (_N, "ESNA", "ESNA1-LF-LD", 400, 93.0, "Nanofiltration", 9500, 75, 500, .15, _I(34, assumed=True)),
    (_N, "ESNA", "ESNA4-LD", 400, 99.0, "Nanofiltration", 11500, 100, 500, .15, _I(34, assumed=True)),
    (_N, "ESNA", "ESNA5-LD", 400, 97.0, "Nanofiltration", 12000, 70, 500, .15, _I(34, assumed=True)),
    (_N, "SWC", "SWC4-LD", 400, 99.8, "SWRO", 6500, 800, 32000, .10, _I(34)),
    (_N, "SWC", "SWC4 MAX", 440, 99.8, "SWRO", 7200, 800, 32000, .10, _I(28)),
    (_N, "SWC", "SWC5-LD", 400, 99.8, "SWRO", 9000, 800, 32000, .10, _I(34)),
    (_N, "SWC", "SWC5 MAX", 440, 99.8, "SWRO", 9900, 800, 32000, .10, _I(28)),
    (_N, "SWC", "SWC6-LD", 400, 99.6, "SWRO", 6000, 600, 32000, .10, _I(34)),
    (_N, "SWC", "SWC6 MAX", 440, 99.6, "SWRO", 6600, 600, 32000, .10, _I(28)),
    # 4-inch elements (IMSDesign list)
    (_N, "CPA", "CPA2-4040", 85, 99.5, "High Rejection BWRO", 2250, 225, 1500, .15, _I(28, 4)),
    (_N, "CPA", "CPA5-LD-4040", 80, 99.7, "High Rejection BWRO", 2100, 225, 1500, .15, _I(34, 4)),
    (_N, "CPA", "CPA7-LD-4040", 80, 99.8, "High Rejection BWRO", 2300, 225, 1500, .15, _I(34, 4)),
    (_N, "ESPA", "ESPA1-LD-4040", 80, 99.4, "Low Energy BWRO", 2450, 150, 1500, .15, _I(34, 4)),
    (_N, "ESPA", "ESPA2-LD-4040", 80, 99.6, "Low Energy BWRO", 2000, 150, 1500, .15, _I(34, 4)),
    (_N, "ESPA", "ESPA4-LD-4040", 80, 99.2, "Ultra Low Energy BWRO", 2350, 100, 500, .15, _I(34, 4)),
    (_N, "LFC", "LFC3-LD-4040", 80, 99.7, "Fouling Resistant BWRO", 2100, 225, 1500, .15, _I(34, 4)),
    (_N, "PRO", "PRO-LF1-4040", 77, 99.7, "High Pressure RO", 1480, 800, 32000, .08, _I(34, 4, assumed=True)),
    (_N, "SanRO", "SanRO-HS2-4", 90, 99.6, "Sanitary BWRO", 3000, 225, 1500, .15, _I(32, 4, assumed=True)),
    (_N, "SanRO", "SanRO-HS-4", 90, 99.7, "Sanitary BWRO", 2200, 225, 1500, .15, _I(32, 4, assumed=True)),
    (_N, "SWC", "SWC5-LD-4040", 80, 99.7, "SWRO", 1750, 800, 32000, .10, _I(34, 4)),
    ("LG Chem", "BW", "LG BW 400 R", 400, 99.60, "High Rejection BWRO", 10500, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 440 R", 440, 99.60, "High Rejection BWRO", 11550, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 440 R G2", 440, 99.78, "High Rejection BWRO", 12650, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 400 R Dura", 400, 99.70, "High Rejection BWRO", 10500, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 440 R Dura", 440, 99.70, "High Rejection BWRO", 11550, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 400 AFR", 400, 99.60, "Fouling Resistant BWRO", 10500, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 400 AFR G2", 400, 99.70, "Fouling Resistant BWRO", 11500, 225, 2000, .15),
    ("LG Chem", "BW", "LG BW 400 ES", 400, 99.60, "Low Energy BWRO", 10500, 150, 2000, .15),
    ("LG Chem", "BW", "LG BW 400 UES", 400, 99.00, "Ultra Low Energy BWRO", 11500, 125, 2000, .15),
    ("LG Chem", "BW", "LG BW 440 UES", 440, 99.00, "Ultra Low Energy BWRO", 12650, 125, 2000, .15),
    ("LG Chem", "SW", "LG SW 400 R", 400, 99.85, "SWRO", 9000, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 R", 440, 99.85, "SWRO", 9900, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 R G2", 400, 99.88, "SWRO", 9000, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 R G2", 440, 99.88, "SWRO", 9900, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 GR", 400, 99.85, "SWRO", 7500, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 GR", 440, 99.85, "SWRO", 8250, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 GR G2", 400, 99.89, "SWRO", 7500, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 GR G2", 440, 99.89, "SWRO", 8250, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 SR", 400, 99.85, "SWRO", 6000, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 SR", 440, 99.85, "SWRO", 6600, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 SR G2", 400, 99.89, "SWRO", 6000, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 SR G2", 440, 99.89, "SWRO", 6600, 800, 32000, .08),
    ("LG Chem", "SW", "LG SW 400 ES", 400, 99.60, "SWRO", 6800, 600, 32000, .08),
    ("LG Chem", "SW", "LG SW 440 ES", 440, 99.60, "SWRO", 7480, 600, 32000, .08),
]
# differences between your original database and the published datasheets (your numbers are kept; see the notes column)
LEGACY_NOTES = {
    "BW30HRLE-440i": "Published (DuPont BWRO list, BW30HRLE-440): stabilized salt rejection 99.3 %, not 99.7 %.",
    "LG BW 400 R G2": "Published (LG Chem): stabilized salt rejection 99.78 %, not 99.6 %.",
}


def builtin_membranes():
    mems = []
    for vendor, series, model, area, rej, typ in LEGACY_MEMBRANES:
        m = dict(MEM_DEFAULTS)
        m.update(vendor=vendor, series=series, model=model, type=typ, area_ft2=float(area), rejection=float(rej),
                 a_w=AW_BY_TYPE.get(typ, 0.125), max_pressure=MAXP_BY_TYPE.get(typ, MAXP_DEFAULT),
                 source="Area, rejection and type from your original database. Permeability and element dP are type-typical values - replace with datasheet data.",
                 notes=LEGACY_NOTES.get(model, ""))
        if model == "ESPA2 MAX":
            m["source"] = "Area, rejection from your database; permeability and element dP calibrated to an IMSDesign run (3 years, 28.8 C)."
        mems.append(m)
    for row in NEW_MEMBRANES:
        vendor, series, model, area, rej, typ, gpd, psi, ppm, rec = row[:10]
        opt = row[10] if len(row) > 10 else {}
        m = dict(MEM_DEFAULTS)
        spacer = f", feed spacer {opt['spacer']} mil" if opt.get("spacer") else ""
        assumed = " - test salinity assumed" if opt.get("assumed") else ""
        m.update(vendor=vendor, series=series, model=model, type=typ, area_ft2=float(area), rejection=float(rej),
                 a_w=round(AW_SCALE * _aw_test(gpd, area, psi, ppm, rec), 4), size_in=float(opt.get("size", 8.0)),
                 max_pressure=1200.0 if (typ in ("SWRO", "High Pressure RO") or model == "ESPA4-LD HP") else MAXP_DEFAULT,
                 source=f"{opt.get('src', 'Manufacturer datasheet')}: active area, rejection and test flow ({gpd:,} gpd at {psi} psi, {ppm:,} ppm NaCl{assumed}){spacer}. "
                        f"Permeability scaled from that test flow to the ESPA2 MAX calibration; element dP is the generic calibration value - verify with the datasheet.",
                 notes="")
        mems.append(m)
    for typ_, aw in (("BWRO", 0.125),):
        m = dict(MEM_DEFAULTS)
        m.update(vendor="Custom", series="Template", model="Template BWRO 400", type=typ_, area_ft2=400.0, rejection=99.5,
                 a_w=aw, source="TEMPLATE - type-typical values, not datasheet data.", notes="")
        mems.append(m)
    return mems


ANTISCALANTS = [  # product, vendor, base dose mg/L, application   (your original database)
    {"product": "Genesys LF", "vendor": "Genesys", "base_dose": 3.0, "application": "General BWRO"},
    {"product": "Genesys SI", "vendor": "Genesys", "base_dose": 4.0, "application": "High Silica"},
    {"product": "Vitec 3000", "vendor": "Avista", "base_dose": 4.0, "application": "General BWRO"},
    {"product": "Vitec 5100", "vendor": "Avista", "base_dose": 5.0, "application": "High Recovery"},
    {"product": "RoClean L403", "vendor": "Kurita", "base_dose": 4.0, "application": "General BWRO"},
    {"product": "Hypersperse MDC220", "vendor": "Veolia", "base_dose": 4.0, "application": "High Sulfate"},
    {"product": "Hypersperse MDC150", "vendor": "Veolia", "base_dose": 3.0, "application": "Municipal Water"},
]


def _clean_membrane(m):
    out = {k: str(m.get(k, "") if m.get(k) is not None else "") for k in MEM_TEXT}
    for k, d in MEM_DEFAULTS.items():
        try:
            v = m.get(k, d)
            out[k] = float(v) if v == v and v is not None else float(d)
        except (TypeError, ValueError):
            out[k] = float(d)
    return out


def load_library():
    mems, vendors, anti, flux = builtin_membranes(), builtin_vendors(), list(ANTISCALANTS), dict(FLUX_DEFAULT)
    try:
        if LIB_FILE.exists():
            d = json.loads(LIB_FILE.read_text(encoding="utf-8"))
            if d.get("membranes"):
                saved = list(d["membranes"])
                if int(d.get("builtin_ver", 1)) < BUILTIN_VER:        # add the built-in models that were introduced after this library was saved
                    by_key = {(m["vendor"], m["model"]): m for m in mems}
                    fixed = []
                    for m in saved:
                        key = (m.get("vendor"), m.get("model"))
                        old = OLD_LEGACY_VALUES.get(key)
                        try:
                            unedited = bool(old) and all(abs(float(m.get(k, -999)) - v) < 1e-9 for k, v in old.items())
                        except (TypeError, ValueError):
                            unedited = False
                        fixed.append(by_key[key] if (unedited and key in by_key) else m)
                    have = {(m.get("vendor"), m.get("model")) for m in fixed}
                    saved = fixed + [m for m in mems if (m["vendor"], m["model"]) not in have]
                mems = saved
            if d.get("vendors"):
                vendors = {**vendors, **d["vendors"]}
            if d.get("antiscalants"):
                anti = d["antiscalants"]
            if d.get("flux"):
                flux = {**flux, **d["flux"]}
    except Exception:
        pass
    mems = [_clean_membrane(m) for m in mems if m.get("vendor") and m.get("model")]
    for name, v in list(vendors.items()):
        full = dict(VENDOR_DEFAULTS)
        full.update(v)
        vendors[name] = full
    return {"membranes": mems, "vendors": vendors, "antiscalants": anti, "flux": flux}


def save_library(mems, vendors, anti, flux, ver=BUILTIN_VER):
    PROJECT_DIR.mkdir(parents=True, exist_ok=True)
    LIB_FILE.write_text(json.dumps({"membranes": mems, "vendors": vendors, "antiscalants": anti, "flux": flux, "builtin_ver": ver}, indent=2),
                        encoding="utf-8")


def vendor_profile(vendor):
    return load_library()["vendors"].get(vendor, dict(VENDOR_DEFAULTS))


def membrane_lookup(vendor, model):
    for m in load_library()["membranes"]:
        if m["vendor"] == vendor and m["model"] == model:
            return m
    return None


def selected_membranes_n(npass):
    """Membrane of every pass: pass 1 as chosen, later passes 'same as pass 1' or their own choice."""
    ms = [membrane_lookup(ss.get("vendor1"), ss.get("model1"))]
    for n in range(2, npass + 1):
        ms.append(ms[0] if ss.get(f"same{n}", True) else membrane_lookup(ss.get(f"vendor{n}"), ss.get(f"model{n}")))
    return ms


def selected_membranes():
    ms = selected_membranes_n(2)
    return ms[0], ms[1]


# =====================================================
# CARBONATE CHEMISTRY  (calibrated to IMSDesign: CO2 = 71.98 mg/L for HCO3 48.8, pH 6.0, 28.8 C)
# =====================================================
def pk1_ro(t):
    return 6.31 - 0.002 * (t - 28.8)


def pk2_ro(t):
    k = t + 273.15
    return 2902.39 / k + 0.02379 * k - 6.4980


def pkw_ro(t):
    k = t + 273.15
    return 4470.99 / k - 6.0875 + 0.01706 * k


def alphas(ph, t):
    h, k1, k2 = 10 ** (-ph), 10 ** (-pk1_ro(t)), 10 ** (-pk2_ro(t))
    d = h * h + k1 * h + k1 * k2
    return h * h / d, k1 * h / d, k1 * k2 / d


def carb_alk(ct_mmol, ph, t):
    a0, a1, a2 = alphas(ph, t)
    return ct_mmol * (a1 + 2 * a2)


def oh_h(ph, t):
    return 1000 * (10 ** (ph - pkw_ro(t)) - 10 ** (-ph))


def solve_ph(alk_meq, ct_mmol, t):
    lo, hi = 2.0, 12.5
    for _ in range(80):
        mid = (lo + hi) / 2
        if carb_alk(ct_mmol, mid, t) + oh_h(mid, t) < alk_meq:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def co2_from_ph(hco3, ph, t):
    return hco3 * (44.0 / 61.0) * 10 ** (pk1_ro(t) - ph)


def tcf(t):
    u = 2640.0 if t >= 25 else 3020.0
    return exp(u * (1 / 298.15 - 1 / (t + 273.15)))


# ---- compositions: dict of mg/L for ION_KEYS + sio2, boron, co2 ----
def blank_comp():
    c = {k: 0.0 for k in ION_KEYS}
    c.update(sio2=0.0, boron=0.0, co2=0.0)
    return c


def comp_alk_ct(c):
    alk = c["hco3"] / 61.017 + 2 * c["co3"] / 60.009
    ct = c["hco3"] / 61.017 + c["co3"] / 60.009 + c["co2"] / 44.009
    return alk, ct


def comp_tds(c):
    return sum(c[k] for k in ION_KEYS) + c["sio2"] + c["boron"]


def comp_osm_bar(c, t):
    mmol = sum(c[k] / ION_MW[k] for k in ION_KEYS) + c["sio2"] / 60.084 + c["boron"] / 10.811
    return mmol / 1000 * R_BAR * (t + 273.15)


def comp_cond(c):
    """Conductivity at 25 C (uS/cm) from the ions (mg/L -> meq/L x equivalent conductance)."""
    return sum(c[k] / ION_MW[k] * ION_Z[k] * ION_LAM[k] for k in ION_KEYS)


def comp_ph(c, t, ph_hint=7.0):
    alk, ct = comp_alk_ct(c)
    return solve_ph(alk, ct, t) if ct > 0 else ph_hint


def lsi_calc(tds, t, ca_mgl, alk_caco3, ph):
    a = (log10(max(tds, 1.0)) - 1) / 10
    b = -13.12 * log10(t + 273) + 34.55
    c_ = log10(max(ca_mgl * 2.497, 0.01)) - 0.4
    d = log10(max(alk_caco3, 0.01))
    phs = 9.3 + a + b - c_ - d
    return ph - phs, phs


KSP = {"CaSO4": 3.14e-5, "BaSO4": 2.4e-11, "SrSO4": 3.44e-7, "CaF2": 3.45e-11}   # BaSO4 tuned to IMSDesign (conservative)


def saturation_pct(c, t, cf=1.0):
    """Indicative saturation (% of Ksp) of sparingly soluble salts at a concentration factor cf (ideal + Davies activity)."""
    mol = {k: c[k] / ION_MW[k] / 1000 * cf for k in ION_KEYS}
    ionic = 0.5 * sum(mol[k] * ION_Z[k] ** 2 for k in ION_KEYS)
    sq = math.sqrt(max(ionic, 0))

    def gamma(z):
        return 10 ** (-0.51 * z * z * (sq / (1 + sq) - 0.3 * ionic))
    g1, g2 = gamma(1), gamma(2)
    out = {"CaSO4": mol["ca"] * g2 * mol["so4"] * g2 / KSP["CaSO4"] * 100,
           "BaSO4": mol["ba"] * g2 * mol["so4"] * g2 / KSP["BaSO4"] * 100,
           "SrSO4": mol["sr"] * g2 * mol["so4"] * g2 / KSP["SrSO4"] * 100,
           "CaF2": mol["ca"] * g2 * (mol["f"] * g1) ** 2 / KSP["CaF2"] * 100}
    s_si = 10 ** (4.566 - 731 / (t + 273.15))
    out["SiO2"] = c["sio2"] * cf / s_si * 100
    return out


# =====================================================
# FEED WATER
# =====================================================
def feed_comp():
    c = blank_comp()
    for k in ION_KEYS:
        c[k] = _f(k)
    c["sio2"], c["boron"] = _f("sio2"), _f("boron")
    t, ph = _f("temp_c", 25.0), _f("ph", 7.0)
    c["co2"] = co2_from_ph(c["hco3"], ph, t) if ss.get("calc_co2", True) else _f("co2")
    return c


def feed_analysis():
    c = feed_comp()
    t, ph = _f("temp_c", 25.0), _f("ph", 7.0)
    rows, cat, an, cond = [], 0.0, 0.0, 0.0
    for kind, table in (("cation", CATIONS), ("anion", ANIONS)):
        for key, label, mw, z, lam in table:
            meq = c[key] * z / mw
            if kind == "cation":
                cat += meq
            else:
                an += meq
            cond += meq * lam
            rows.append({"key": key, "ion": label, "kind": kind, "mg": c[key], "meq": meq, "caco3": meq * 50.04})
    cond += 1000 * 10 ** (-ph) * 349.8 + 1000 * 10 ** (ph - 14) * 198.6
    tds = comp_tds(c)
    hardness = c["ca"] * 2.497 + c["mg"] * 4.118
    alk = c["hco3"] * 50 / 61.017 + c["co3"] * 50 / 30.0
    lsi, phs = lsi_calc(tds, t, c["ca"], alk, ph)
    cbe = (cat - an) / (cat + an) * 100 if (cat + an) > 0 else 0.0
    return {"c": c, "rows": rows, "tds": tds, "hardness": hardness, "alk": alk, "cond": cond, "cbe": cbe, "cat": cat,
            "an": an, "osm_bar": comp_osm_bar(c, t), "lsi": lsi, "phs": phs, "ph": ph, "t": t,
            "sat": saturation_pct(c, t), "resistivity": 1e6 / cond if cond > 0 else 0.0}


# =====================================================
# CHEMICAL pH ADJUSTMENT AND PERMEATE COMPOSITION
# =====================================================
ACIDS = {"H2SO4": (49.04, "so4", 96.06 / 98.08), "HCl": (36.46, "cl", 35.453 / 36.46)}
CHEM_DEFAULTS = {"H2SO4": (98.0, 1.84), "HCl": (32.0, 1.16), "NaOH": (50.0, 1.52), "None": (100.0, 1.0)}


def ph_adjust(comp, ph_now, ph_target, chem, t):
    """Dose (mg/L, 100 %) of acid / NaOH that brings a stream from ph_now to ph_target (alkalinity balance, total carbonate conserved)."""
    c = dict(comp)
    out = {"dose": 0.0, "chem": chem, "note": "", "ph": ph_now, "comp": c}
    if chem in (None, "None", ""):
        return out
    alk0, ct = comp_alk_ct(c)
    alk0 += oh_h(ph_now, t)
    delta = carb_alk(ct, ph_target, t) + oh_h(ph_target, t) - alk0       # + = base needed, - = acid needed
    dose = 0.0
    if chem in ACIDS:
        eq, ion, frac = ACIDS[chem]
        if delta < 0:
            dose = -delta * eq
            c[ion] += dose * frac
        else:
            out["note"] = f"Target pH {ph_target:.2f} is above the stream pH {ph_now:.2f} - {chem} cannot raise pH."
    elif chem == "NaOH":
        if delta > 0:
            dose = delta * 40.0
            c["na"] += dose * 22.99 / 40.0
        else:
            out["note"] = f"Target pH {ph_target:.2f} is below the stream pH {ph_now:.2f} - NaOH cannot lower pH."
    if dose > 0:
        a0, a1, a2 = alphas(ph_target, t)
        c["hco3"], c["co3"], c["co2"] = ct * a1 * 61.017, ct * a2 * 60.009, ct * a0 * 44.009
        out["ph"] = ph_target
    out["dose"], out["comp"] = dose, c
    return out


def boron_rejection(ph):
    for lim, rej in ((7.5, 85.0), (8.0, 90.0), (8.5, 93.0), (9.0, 95.0), (9.5, 97.0)):
        if ph < lim:
            return rej
    return 98.5


def permeate_comp(c, y, rej_pct, age, sp_inc, ph_feed):
    """Permeate composition: passage x flux-averaged feed-concentrate concentration (log-mean)."""
    lm = log(1 / (1 - y)) / y if 0 < y < 1 else 1.0
    sp = (1 - rej_pct / 100) * (1 + sp_inc / 100) ** age
    if comp_tds(c) < SP_DILUTE_TDS:
        sp *= SP_DILUTE_FACTOR
    sp = min(sp, 1.0)
    p = blank_comp()
    for k in ION_KEYS:
        p[k] = c[k] * lm * sp
    p["sio2"] = c["sio2"] * lm * min(sp * SILICA_SP_FACTOR, 1.0)
    p["boron"] = c["boron"] * lm * (1 - boron_rejection(ph_feed) / 100)
    p["co2"] = c["co2"] * CO2_PASSAGE
    return p


def conc_comp(c, p, f, p_cum):
    cc = f - p_cum
    if cc <= 0:
        return dict(c)
    return {k: max((f * c[k] - p_cum * p[k]) / cc, 0.0) for k in c}


# =====================================================
# PASS DESIGN: flows, stages, flux, hydraulics
# =====================================================
def get_stages(n):
    ns = int(max(min(_f(f"p{n}_stages", 3 if n == 1 else 2), 3), 1))
    out = []
    for i in range(1, ns + 1):
        dv, de = DEF_STAGE[n][i]
        out.append((max(int(_f(f"p{n}_s{i}_v", dv)), 1), max(int(_f(f"p{n}_s{i}_e", de)), 1)))
    return out


def pass_calc(f_m3h, p_m3h, stages, mem, osm_feed_bar, t, age, decl, perm_psi, rec_el=0.10):
    a_el = mem["area_ft2"]
    f, p = f_m3h * GPM, p_m3h * GPM
    areas = [v * e * a_el for v, e in stages]
    area = sum(areas)
    flux = p * 1440 / area if area > 0 else 0.0
    y = p / f if f > 0 else 0.0
    ff = (1 - decl / 100) ** age
    ndp = flux / (mem["a_w"] * tcf(t) * ff) if mem["a_w"] > 0 and ff > 0 else 0.0
    rows, feed_i, p_cum, dp_total = [], f, 0.0, 0.0
    n_series = 0
    for i, ((v, e), a) in enumerate(zip(stages, areas), start=1):
        perm_i = p * a / area if area > 0 else 0.0
        conc_i = feed_i - perm_i
        feed_v, conc_v = feed_i / v, conc_i / v
        lead = (flux * a_el / 1440) / feed_v * 100 if feed_v > 0 else 0.0
        avg_v = (feed_v + conc_v) / 2
        dp_el = mem["dp_ref"] * (avg_v / (50.0 * (float(mem.get("size_in", 8.0)) / 8.0) ** 2)) ** DP_EXPONENT     # reference flow scales with the element cross-section
        rows.append({"stage": i, "vessels": v, "elements": e, "area": a, "feed": feed_i, "perm": perm_i, "conc": conc_i,
                     "feed_v": feed_v, "conc_v": conc_v, "lead_rec": lead, "dp_el": dp_el, "dp_stage": dp_el * e})
        feed_i, p_cum, dp_total, n_series = conc_i, p_cum + perm_i, dp_total + dp_el * e, n_series + e
    lm = log(1 / (1 - y)) / y if 0 < y < 1 else 1.0
    pi_avg = osm_feed_bar * lm * PSI
    pf = ndp + pi_avg + perm_psi + dp_total / 2
    pr = pf
    for r in rows:
        r["p_in"] = pr
        pr -= r["dp_stage"]
    return {"f": f, "p": p, "c": f - p, "f_m3h": f_m3h, "p_m3h": p_m3h, "c_m3h": f_m3h - p_m3h, "y": y, "area": area,
            "n_el": sum(v * e for v, e in stages), "n_vessels": sum(v for v, e in stages), "flux": flux, "ff": ff,
            "tcf": tcf(t), "ndp": ndp, "pi_avg": pi_avg, "dp_total": dp_total, "pf": pf, "rows": rows,
            "n_series": n_series, "rec_capacity": (1 - (1 - rec_el) ** n_series) * 100}


def pass_default(n, what):
    """Default per-pass inputs: pass 1 treats the raw water, later passes treat RO permeate."""
    return {"rec": 75.0 if n == 1 else 85.0, "age": 3.0, "decl": 7.0 if n == 1 else 3.0, "sp": 7.0 if n == 1 else 5.0}[what]


def design_calc():
    """Complete design for 1-4 passes: flows, chemistry-adjusted streams, hydraulics, power. Returns None when the design is incomplete."""
    fa = feed_analysis()
    passes = int(min(max(_f("passes", 1), 1), MAX_PASSES))
    mems = selected_membranes_n(passes)
    if any(m is None for m in mems):
        return None
    t = fa["t"]
    q = max(_f("product_flow", 0.0), 0.0)
    if q <= 0:
        return None
    rec = [min(max(_f(f"p{n}_rec", pass_default(n, "rec")), 1), 99) / 100 for n in range(1, passes + 1)]
    # flows (product driven): the last pass makes the plant product and every pass is fed with the permeate of the pass before it
    p_m3h, f_m3h, c_m3h = [0.0] * passes, [0.0] * passes, [0.0] * passes
    p_m3h[-1] = q
    for i in range(passes - 1, -1, -1):
        f_m3h[i] = p_m3h[i] / rec[i]
        c_m3h[i] = f_m3h[i] - p_m3h[i]
        if i > 0:
            p_m3h[i - 1] = f_m3h[i]
    recycle = passes >= 2 and bool(ss.get("recycle", True))
    raw = f_m3h[0] - (sum(c_m3h[1:]) if recycle else 0.0)
    perm_psi = _f("perm_pressure", 0.0)

    # ---- chemistry and hydraulics, pass by pass ----
    raw_comp = fa["c"]
    comp_in, ph_in = raw_comp, fa["ph"]
    pl = []
    for i in range(passes):
        n = i + 1
        if n == 1:
            chem, target = ss.get("p1_chem", "None"), _f("p1_ph", fa["ph"])
        else:
            chem, target = ss.get(f"p{n}_chem", "NaOH" if n == 2 else "None"), _f(f"p{n}_ph", 8.2)
        adj = ph_adjust(comp_in, ph_in, target, chem, t)
        feed, ph_feed = adj["comp"], adj["ph"]
        age, decl, spi = _f(f"age{n}", pass_default(n, "age")), _f(f"decl{n}", pass_default(n, "decl")), _f(f"sp{n}", pass_default(n, "sp"))
        calc = pass_calc(f_m3h[i], p_m3h[i], get_stages(n), mems[i], comp_osm_bar(feed, t), t, age, decl, perm_psi,
                         REC_PER_ELEMENT[1 if n == 1 else 2])
        perm = permeate_comp(feed, calc["y"], mems[i]["rejection"], age, spi, ph_feed)
        stage_conc, pc = [], 0.0
        for r in calc["rows"]:
            pc += r["perm"]
            stage_conc.append(conc_comp(feed, perm, calc["f"], pc))
        conc = stage_conc[-1]
        ph_perm = comp_ph(perm, t, 5.5 if n == 1 else 6.0)
        pl.append({"n": n, "mem": mems[i], "adj": adj, "feed": feed, "ph_feed": ph_feed, "perm": perm, "ph_perm": ph_perm,
                   "conc": conc, "ph_conc": comp_ph(conc, t, ph_feed + 0.3), "stage_conc": stage_conc, "calc": calc})
        comp_in, ph_in = perm, ph_perm

    first, last = pl[0], pl[-1]
    second = pl[1] if passes >= 2 else None
    out = {"fa": fa, "m1": mems[0], "m2": mems[1] if passes >= 2 else mems[0], "mems": mems, "pl": pl, "passes": passes, "t": t,
           "q": q, "raw": raw, "recycle": recycle, "raw_comp": raw_comp, "overall_rec": q / raw * 100 if raw > 0 else 0.0,
           # pass 1 / pass 2 keys kept for the older pages
           "adj1": first["adj"], "feed1": first["feed"], "perm1": first["perm"], "conc1": first["conc"], "stage_conc1": first["stage_conc"],
           "p1": first["calc"], "ph1": first["ph_feed"], "perm1_ph": first["ph_perm"],
           "adj2": second["adj"] if second else None, "feed2": second["feed"] if second else None,
           "perm2": second["perm"] if second else None, "conc2": second["conc"] if second else None,
           "stage_conc2": second["stage_conc"] if second else [], "p2": second["calc"] if second else None,
           "ph2": second["ph_feed"] if second else None, "product": last["perm"], "product_ph": last["ph_perm"]}

    # ---- power (IMSDesign method) ----
    ep, em, ev = _f("eff_pump", 87.0) / 100, _f("eff_motor", 95.0) / 100, _f("eff_vfd", 97.0) / 100
    eff = max(ep * em * ev, 1e-6)
    for e in pl:
        pdict = e["calc"]
        kw = pdict["f"] * pdict["pf"] / 1714 * HP_KW / eff
        pdict["kw"], pdict["bhp"] = kw, kw / HP_KW
    out["power_kw"] = sum(e["calc"]["kw"] for e in pl)
    prod_kgal_h = q * GPM * 60 / 1000
    out["spec_kwh_kgal"] = out["power_kw"] / prod_kgal_h if prod_kgal_h > 0 else 0.0
    out["spec_kwh_m3"] = out["power_kw"] / q if q > 0 else 0.0
    # ---- concentrate scaling indicators (pass 1 concentrate: the highest salinity in the plant) ----
    p1 = first["calc"]
    cf = p1["f"] / p1["c"] if p1["c"] > 0 else 1.0
    out["cf"] = cf
    out["sat_conc"] = saturation_pct(first["feed"], t, cf)
    conc1 = first["conc"]
    alk_c = conc1["hco3"] * 50 / 61.017 + conc1["co3"] * 50 / 30.0
    out["lsi_conc"], out["phs_conc"] = lsi_calc(comp_tds(conc1), t, conc1["ca"], alk_c, first["ph_conc"])
    out["ph_conc"] = first["ph_conc"]
    out["tds_product"] = comp_tds(out["product"])
    return out


def guideline_flux(water, pass_no, vendor):
    """Recommended maximum flux (gfd). Pass 2 is fed with RO permeate, so it uses the RO/NF-permeate row (pass-2 column)."""
    lib = load_library()
    if pass_no >= 2:
        water = "RO/NF Permeate"
    row = lib["flux"].get(water, FLUX_DEFAULT.get(water, [12.0, 15.0]))
    return float(row[0 if pass_no == 1 else 1]) * float(lib["vendors"].get(vendor, VENDOR_DEFAULTS).get("flux_scale", 1.0))


def run_checks(d):
    """Design cautions. Each item: level ok|warn|bad|info. 'bad' (red) means the design should not be used as is."""
    checks = []

    def add(level, text):
        checks.append({"level": level, "text": text})
    if not d:
        add("bad", "The design is incomplete - select the membrane, enter the product flow and the stage layout.")
        return checks
    fa, water = d["fa"], ss.get("water_type", "Municipal Water")
    t = d["t"]
    for n, pd_, mem in [(e["n"], e["calc"], e["mem"]) for e in d["pl"]]:
        vp = vendor_profile(mem["vendor"])
        guide = guideline_flux(water, n, mem["vendor"])
        fl = pd_["flux"]
        basis = water if n == 1 else "RO permeate feed"
        if fl > guide * 1.15:
            add("bad", f"PASS {n} FLUX TOO HIGH: {fl:.1f} gfd exceeds the recommended {guide:.1f} gfd for {basis} "
                       f"by {(fl / guide - 1) * 100:.0f} %. Add elements (needs about {math.ceil(pd_['n_el'] * fl / guide)} in total).")
        elif fl > guide:
            add("warn", f"Pass {n} flux {fl:.1f} gfd is above the recommended {guide:.1f} gfd for {basis} "
                        f"(+{(fl / guide - 1) * 100:.0f} %); about {math.ceil(pd_['n_el'] * fl / guide)} elements would meet it.")
        elif fl < guide * 0.5:
            add("info", f"Pass {n} flux {fl:.1f} gfd is low (below 50 % of {guide:.1f} gfd): the membrane area may be oversized.")
        else:
            add("ok", f"Pass {n} flux {fl:.1f} gfd is within the recommended {guide:.1f} gfd for {basis}.")
        # per-vessel hydraulics
        worst_f = max(r["feed_v"] for r in pd_["rows"])
        sz = (float(mem.get("size_in", 8.0)) / 8.0) ** 2          # vendor flow limits are for 8-inch elements; scaled with the cross-section for 4-inch
        lim_f = vp["max_feed_gpm"] * sz
        if worst_f > lim_f:
            add("bad", f"PASS {n} FEED FLOW PER VESSEL {worst_f:.1f} gpm exceeds the {lim_f:.0f} gpm maximum - add vessels in the first stage.")
        elif worst_f > 0.9 * lim_f:
            add("warn", f"Pass {n} feed flow per vessel {worst_f:.1f} gpm is above 90 % of the {lim_f:.0f} gpm maximum.")
        last = pd_["rows"][-1]
        lim_c = vp["min_conc_gpm"] * sz
        if last["conc_v"] < lim_c:
            add("bad", f"PASS {n} CONCENTRATE FLOW PER VESSEL {last['conc_v']:.1f} gpm is below the {lim_c:.0f} gpm minimum - reduce recovery or vessels in the last stage.")
        elif last["conc_v"] < 1.1 * lim_c:
            add("warn", f"Pass {n} concentrate flow per vessel {last['conc_v']:.1f} gpm is close to the {lim_c:.0f} gpm minimum.")
        lead = pd_["rows"][0]["lead_rec"]
        if lead > vp["max_lead_rec"]:
            add("bad", f"PASS {n} LEAD-ELEMENT RECOVERY {lead:.1f} % exceeds {vp['max_lead_rec']:.0f} %.")
        elif lead > 0.9 * vp["max_lead_rec"]:
            add("warn", f"Pass {n} lead-element recovery {lead:.1f} % is close to the {vp['max_lead_rec']:.0f} % limit.")
        worst_dp = max(r["dp_stage"] for r in pd_["rows"])
        if worst_dp > vp["max_dp_vessel"]:
            add("bad", f"PASS {n} VESSEL PRESSURE DROP {worst_dp:.1f} psi exceeds {vp['max_dp_vessel']:.0f} psi.")
        if max(r["dp_el"] for r in pd_["rows"]) > vp["max_dp_element"]:
            add("bad", f"PASS {n} ELEMENT PRESSURE DROP exceeds {vp['max_dp_element']:.0f} psi.")
        cap = pd_["rec_capacity"]
        rec = pd_["y"] * 100
        if rec > cap + 10:
            add("bad", f"PASS {n} RECOVERY {rec:.0f} % is too high for {pd_['n_series']} elements in series (about {cap:.0f} % possible) - add a stage or elements.")
        elif rec > cap + 3:
            add("warn", f"Pass {n} recovery {rec:.0f} % is at the limit for {pd_['n_series']} elements in series (about {cap:.0f} %).")
        if pd_["pf"] > mem["max_pressure"]:
            add("bad", f"PASS {n} FEED PRESSURE {pd_['pf']:.0f} psi exceeds the {mem['max_pressure']:.0f} psi limit of {mem['model']}.")
        if mem["type"] == "SWRO" and water != "Sea Water":
            add("warn", f"Pass {n}: {mem['model']} is a seawater membrane but the water type is {water}.")
        if mem["type"] != "SWRO" and water == "Sea Water":
            add("bad", f"PASS {n}: {mem['model']} is a brackish-water membrane - not suitable for Sea Water.")
        if str(mem.get("source", "")).upper().startswith("TEMPLATE"):
            add("warn", f"{mem['model']}: TEMPLATE data - replace it on the Library page.")
        if "nano" in str(mem.get("type", "")).lower():
            add("warn", f"Pass {n}: {mem['model']} is a nanofiltration membrane - the salt-passage model treats all ions alike, so divalent-ion "
                        f"rejection and product TDS are only indicative; confirm with the vendor software.")
    vp1 = vendor_profile(d["m1"]["vendor"])
    if t > vp1["max_temp_c"]:
        add("bad", f"FEED TEMPERATURE {t:.1f} °C exceeds the {vp1['max_temp_c']:.0f} °C maximum.")
    ph_ = d["ph1"]
    if ph_ < vp1["ph_min"] or ph_ > vp1["ph_max"]:
        add("bad", f"PASS 1 FEED pH {ph_:.2f} is outside the {vp1['ph_min']:.0f}-{vp1['ph_max']:.0f} range.")
    sdi, sdi_max = _f("sdi", 0.0), vp1["max_sdi"]
    if sdi > sdi_max:
        add("bad", f"FEED SDI {sdi:.1f} exceeds {sdi_max:.0f}. Recommended for {water}: {SDI_REQ.get(water, '')}.")
    elif sdi > 0:
        add("ok", f"Feed SDI {sdi:.1f} (recommended for {water}: {SDI_REQ.get(water, '')}).")
    if _f("free_cl", 0.0) > vp1["max_free_cl"] and smbs_dose() <= 0:
        add("bad", "FREE CHLORINE will oxidise the polyamide membrane - dose SMBS.")
    elif _f("free_cl", 0.0) > vp1["max_free_cl"]:
        add("ok", f"Free chlorine {_f('free_cl', 0.0):.2f} mg/L is removed with SMBS.")
    if fa["c"]["fe"] > 0.1 or fa["c"]["mn"] > 0.05:
        add("warn", f"Iron {fa['c']['fe']:.2f} / manganese {fa['c']['mn']:.2f} mg/L may foul the membranes - add iron/manganese removal.")
    # scaling
    sat = d["sat_conc"]
    flagged = [k for k, v in sat.items() if v > 100]
    dose_as = chemical_program(d)["antiscalant_dose"]
    if flagged and dose_as <= 0:
        add("bad", "SCALING: " + ", ".join(f"{k} {sat[k]:.0f} %" for k in flagged) + " in the concentrate - antiscalant is required.")
    elif flagged:
        add("warn", "Scaling potential in the concentrate: " + ", ".join(f"{k} {sat[k]:.0f} %" for k in flagged) + f" - antiscalant {dose_as:.1f} mg/L applied.")
    else:
        add("ok", "No sparingly-soluble salt exceeds saturation in the concentrate.")
    if d["lsi_conc"] > 0 and d["adj1"]["dose"] <= 0 and dose_as <= 0:
        add("warn", f"Concentrate LSI {d['lsi_conc']:+.2f} > 0: CaCO3 scaling - add acid or antiscalant.")
    elif d["lsi_conc"] > 0:
        add("info", f"Concentrate LSI {d['lsi_conc']:+.2f} > 0 - controlled with antiscalant / pH adjustment.")
    # product quality target
    target = _f("target_tds", 0.0)
    if target > 0:
        if d["tds_product"] > target:
            add("bad" if d["passes"] >= 2 else "warn",
                f"PRODUCT TDS {d['tds_product']:.1f} mg/L exceeds the target {target:.1f} mg/L" +
                (" - add a second pass." if d["passes"] == 1 else "."))
        else:
            add("ok", f"Product TDS {d['tds_product']:.1f} mg/L meets the target {target:.1f} mg/L.")
    if abs(fa["cbe"]) > 10:
        add("warn", f"Feed charge balance error {fa['cbe']:+.1f} % - check the analysis.")
    for e in d["pl"]:
        if e["adj"]["note"]:
            add("warn", e["adj"]["note"])
    return checks


def overall(checks):
    lv = [c["level"] for c in checks]
    return "bad" if "bad" in lv else ("warn" if "warn" in lv else "ok")


# =====================================================
# CHEMICALS (every chemical with dose, consumption, solution volume and cost)
# =====================================================
POST_CHEMS = [  # key, label, ion effects per mg of 100 % chemical
    ("pt_naoh", "NaOH", 40.0),
    ("pt_nahco3", "NaHCO3", 84.007),
    ("pt_na2co3", "Na2CO3", 105.99),
    ("pt_caoh2", "Ca(OH)2", 74.093),
    ("pt_h2so4", "H2SO4", 98.08),
    ("pt_hcl", "HCl", 36.46),
    ("pt_co2", "CO2", 44.009),
    ("pt_naocl", "NaOCl", 74.44),
]


def antiscalant_recommend(d, product):
    if not product:
        return 0.0
    base = float(product.get("base_dose", 3.0))
    n_flag = sum(1 for v in d["sat_conc"].values() if v > 100)
    dose = base + 0.5 * n_flag + (0.5 if d["lsi_conc"] > 0 else 0.0) + (0.5 if d["overall_rec"] > 80 else 0.0)
    return min(dose, 2 * base)


def post_treatment(d):
    """Final water after the post-treatment doses (mg/L, 100 %): composition, pH, alkalinity, hardness, LSI."""
    t = d["t"]
    c = dict(d["product"])
    ph0 = d["product_ph"]
    alk, ct = comp_alk_ct(c)
    alk += oh_h(ph0, t)
    dose = {k: _f(k, 0.0) for k, _, _ in POST_CHEMS}
    alk += dose["pt_naoh"] / 40.0 + dose["pt_nahco3"] / 84.007 + 2 * dose["pt_na2co3"] / 105.99 + 2 * dose["pt_caoh2"] / 74.093 \
        - 2 * dose["pt_h2so4"] / 98.08 - dose["pt_hcl"] / 36.46
    ct += dose["pt_nahco3"] / 84.007 + dose["pt_na2co3"] / 105.99 + dose["pt_co2"] / 44.009
    c["na"] += dose["pt_naoh"] * 22.99 / 40.0 + dose["pt_nahco3"] * 22.99 / 84.007 + dose["pt_na2co3"] * 45.98 / 105.99 \
        + dose["pt_naocl"] * 22.99 / 74.44
    c["ca"] += dose["pt_caoh2"] * 40.078 / 74.093
    c["so4"] += dose["pt_h2so4"] * 96.06 / 98.08
    c["cl"] += dose["pt_hcl"] * 35.453 / 36.46 + dose["pt_naocl"] * 35.453 / 74.44
    ph = solve_ph(alk, ct, t) if ct > 0 or alk != 0 else ph0
    a0, a1, a2 = alphas(ph, t)
    c["hco3"], c["co3"], c["co2"] = ct * a1 * 61.017, ct * a2 * 60.009, ct * a0 * 44.009
    tds = comp_tds(c)
    alk_caco3 = c["hco3"] * 50 / 61.017 + c["co3"] * 50 / 60.009 * 2
    lsi, phs = lsi_calc(tds, t, c["ca"], max(alk_caco3, 0.01), ph)
    return {"comp": c, "ph": ph, "tds": tds, "alk": alk_caco3, "hardness": c["ca"] * 2.497 + c["mg"] * 4.118, "lsi": lsi,
            "phs": phs, "dose": dose, "cond": comp_cond(c), "any": any(v > 0 for v in dose.values())}


def smbs_dose():
    """SMBS (Na2S2O5) dose in mg/L (100 %): manual dose, or free chlorine x ratio."""
    if str(ss.get("smbs_mode", "Manual dose")).startswith("Manual"):
        return _f("smbs_dose_manual", 3.0)
    return _f("free_cl", 0.0) * _f("smbs_ratio", 3.0)


def chemical_program(d):
    """Rows for every chemical: dose, flow, kg/h (100 %), solution kg/h and L/h, kg/day, cost per day."""
    g = _f
    rows = []
    lib = load_library()
    product = next((a for a in lib["antiscalants"] if a.get("product") == ss.get("as_product")), None)
    rec = antiscalant_recommend(d, product)
    as_dose = g("as_dose_manual", 0.0) if str(ss.get("as_mode", "Recommended")).startswith("Manual") else rec

    def add(name, point, dose, flow, conc, sg, cost_key):
        kg_h = dose * flow / 1000
        sol = kg_h / (conc / 100) if conc > 0 else 0.0
        lph = sol / sg if sg > 0 else 0.0
        cost_kg = g(cost_key, 0.0)
        rows.append({"name": name, "point": point, "dose": dose, "flow": flow, "kg_h": kg_h, "conc": conc, "sg": sg,
                     "sol_kg_h": sol, "l_h": lph, "kg_day": kg_h * 24, "sol_kg_day": sol * 24, "l_day": lph * 24,
                     "cost_day": sol * 24 * cost_kg, "cost_kg": cost_kg})

    raw = d["raw"]
    add("SMBS (Na2S2O5)", "RO feed (dechlorination)", smbs_dose(), raw, g("smbs_conc", 10.0), g("smbs_sg", 1.10), "cost_smbs")
    add("Antiscalant", "RO feed", as_dose, raw, g("as_conc", 40.0), g("as_sg", 1.0), "cost_as")
    add("NaOCl", "RO feed (disinfection)", g("naocl_dose", 0.0), raw, g("naocl_conc", 10.0), g("naocl_sg", 1.30), "cost_naocl")
    if d["adj1"]["chem"] in ACIDS or d["adj1"]["chem"] == "NaOH":
        c1, s1 = g("p1_conc", CHEM_DEFAULTS[d["adj1"]["chem"]][0]), g("p1_sg", CHEM_DEFAULTS[d["adj1"]["chem"]][1])
        add(f"{d['adj1']['chem']} (pass 1 pH)", "RO feed", d["adj1"]["dose"], raw, c1, s1, "cost_p1")
    for e in d["pl"][1:]:
        n, adj = e["n"], e["adj"]
        if adj["chem"] not in ("None", None, ""):
            dc = CHEM_DEFAULTS.get(adj["chem"], (100.0, 1.0))
            add(f"{adj['chem']} (pass {n} pH)", f"Pass {n} feed", adj["dose"], d["pl"][n - 2]["calc"]["p_m3h"],
                g(f"p{n}_conc", dc[0]), g(f"p{n}_sg", dc[1]), f"cost_p{n}")
    for key, label, mw in POST_CHEMS:
        if g(key, 0.0) > 0:
            add(f"{label} (post-treatment)", "Product", g(key, 0.0), d["q"], 100.0, 1.0, "cost_" + key)
    q = d["q"]
    for r in rows:
        r["cost_m3"] = r["cost_day"] / (q * 24) if q > 0 else 0.0
    return {"rows": rows, "antiscalant_dose": as_dose, "antiscalant_rec": rec, "product": product,
            "cost_day": sum(r["cost_day"] for r in rows), "cost_m3": sum(r["cost_m3"] for r in rows)}


# =====================================================
# WATER QUALITY TABLE (IMSDesign style)
# =====================================================
QUALITY_KEYS = [k for k in ION_KEYS] + ["sio2", "boron", "co2"]
QUALITY_LABEL = {**ION_LABEL, "sio2": "SiO2", "boron": "B", "co2": "CO2"}


def quality_table(d):
    cols = [("Raw water", d["raw_comp"], d["fa"]["ph"]), ("RO feed", d["feed1"], d["ph1"])]
    for e in d["pl"]:
        n = e["n"]
        if n > 1:
            cols.append((f"Pass {n} feed", e["feed"], e["ph_feed"]))
        cols += [(f"Pass {n} permeate", e["perm"], e["ph_perm"]), (f"Pass {n} concentrate", e["conc"], e["ph_conc"])]
    data = {"Parameter": [QUALITY_LABEL[k] for k in QUALITY_KEYS] + ["TDS", "pH"]}
    for name, comp, ph in cols:
        data[name] = [round(comp[k], 3) for k in QUALITY_KEYS] + [round(comp_tds(comp), 2), round(ph, 2)]
    df = pd.DataFrame(data)
    keep = df[(df["Parameter"].isin(["TDS", "pH"])) | (df.drop(columns="Parameter").abs().sum(axis=1) > 0)]
    return keep.reset_index(drop=True)


def _basic_quality(c, ph):
    return {"tds": comp_tds(c), "ph": ph, "cond": comp_cond(c), "hardness": c["ca"] * 2.497 + c["mg"] * 4.118,
            "alk": c["hco3"] * 50 / 61.017 + c["co3"] * 50 / 30.0}


def effluent_summary(d):
    """Treated water after RO: flows, product (permeate) and concentrate (reject) quality, rejection by species.
    The discharged concentrate is the pass-1 concentrate, plus the pass-2 concentrate when it is not recycled."""
    t = d["t"]
    streams = [(d["pl"][0]["conc"], d["pl"][0]["calc"]["c_m3h"])]
    if not d["recycle"]:
        streams += [(e["conc"], e["calc"]["c_m3h"]) for e in d["pl"][1:]]
    conc_flow = sum(f for _, f in streams)
    conc = {k: sum(c[k] * f for c, f in streams) / conc_flow for k in streams[0][0]} if conc_flow > 0 else dict(streams[0][0])
    raw, prod = d["raw_comp"], d["product"]
    ph_conc = comp_ph(conc, t, d["ph_conc"])
    pt = post_treatment(d)
    return {"flow_raw": d["raw"], "flow_prod": d["q"], "flow_conc": conc_flow, "rec": d["overall_rec"],
            "raw": raw, "prod": prod, "conc": conc, "post": pt if pt["any"] else None,
            "q": {"raw": _basic_quality(raw, d["fa"]["ph"]), "prod": _basic_quality(prod, d["product_ph"]),
                  "conc": _basic_quality(conc, ph_conc)},
            "osm_conc_psi": comp_osm_bar(conc, t) * PSI, "cf": d["cf"], "lsi_conc": d["lsi_conc"], "sat_conc": d["sat_conc"],
            "tds_rej": (1 - comp_tds(prod) / comp_tds(raw)) * 100 if comp_tds(raw) > 0 else 0.0}


def effluent_rows(e):
    """One row per species / parameter: raw water, RO product, rejection %, (post-treated product), concentrate, concentration factor."""
    post, rows = e["post"], []

    def add(param, unit, raw, prod, conc, post_v=None, show_rej=True):
        ok = show_rej and raw and raw > 0
        rows.append({"param": param, "unit": unit, "raw": raw, "prod": prod, "conc": conc, "post": post_v,
                     "rej": (1 - prod / raw) * 100 if ok else None, "factor": conc / raw if ok else None})
    for k in QUALITY_KEYS:
        if e["raw"][k] > 0 or e["prod"][k] > 0:
            add(QUALITY_LABEL[k], "mg/L", e["raw"][k], e["prod"][k], e["conc"][k], post["comp"][k] if post else None)
    q = e["q"]
    add("TDS", "mg/L", q["raw"]["tds"], q["prod"]["tds"], q["conc"]["tds"], post["tds"] if post else None)
    add("pH", "-", q["raw"]["ph"], q["prod"]["ph"], q["conc"]["ph"], post["ph"] if post else None, False)
    add("Conductivity", "µS/cm", q["raw"]["cond"], q["prod"]["cond"], q["conc"]["cond"], post["cond"] if post else None)
    add("Hardness", "mg/L as CaCO3", q["raw"]["hardness"], q["prod"]["hardness"], q["conc"]["hardness"], post["hardness"] if post else None)
    add("Alkalinity", "mg/L as CaCO3", q["raw"]["alk"], q["prod"]["alk"], q["conc"]["alk"], post["alk"] if post else None)
    return rows


# =====================================================
# PDF REPORT
# =====================================================
NAVY = colors.HexColor("#14283A")
BLUE = colors.HexColor("#0E7FA8")
LIGHT = colors.HexColor("#EEF4F8")
GRID = colors.HexColor("#BCCBD8")


def build_pdf_report():
    g = ss.get
    d = design_calc()
    checks = run_checks(d)
    status = overall(checks)
    project = g("project_name", "HSKH RO Project")
    now = datetime.now().strftime("%d %b %Y  %H:%M")
    styles = getSampleStyleSheet()
    s_title = ParagraphStyle("t", parent=styles["Title"], textColor=NAVY, fontSize=22, alignment=0, spaceAfter=2)
    s_sub = ParagraphStyle("s", parent=styles["Normal"], textColor=colors.grey, fontSize=10)
    s_h = ParagraphStyle("h", parent=styles["Heading2"], textColor=BLUE, fontSize=13, spaceBefore=12, spaceAfter=5)
    s_cell = ParagraphStyle("c", parent=styles["Normal"], fontSize=8.5, leading=10.5)
    s_small = ParagraphStyle("sm", parent=styles["Normal"], fontSize=8, leading=10, textColor=colors.HexColor("#555555"))

    def P(text, st_=s_cell):
        return Paragraph(escape(ascii_txt(text)), st_)

    def tbl(rows, header=None, widths=None, wrap_cols=(), font=8.5):
        data = [[ascii_txt(c) for c in header]] if header else []
        for r in rows:
            data.append([P(c) if (j in wrap_cols and isinstance(c, str)) else ascii_txt(c) for j, c in enumerate(r)])
        t = Table(data, colWidths=widths, repeatRows=1 if header else 0)
        style = [("FONTNAME", (0, 0), (-1, -1), "Helvetica"), ("FONTSIZE", (0, 0), (-1, -1), font),
                 ("GRID", (0, 0), (-1, -1), 0.4, GRID), ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                 ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]
        start = 0
        if header:
            start = 1
            style += [("BACKGROUND", (0, 0), (-1, 0), BLUE), ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
                      ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold")]
        for i in range(start, len(data)):
            if (i - start) % 2 == 1:
                style.append(("BACKGROUND", (0, i), (-1, i), LIGHT))
        t.setStyle(TableStyle(style))
        return t

    W = 174 * mm
    kv = [W * 0.42, W * 0.58]
    story = [Paragraph(escape(f"{APP_TITLE} - Design Report"), s_title),
             Paragraph(escape(ascii_txt(f"{project}  |  {now}")), s_sub), Spacer(1, 6)]

    def section(title, rows, header=None, widths=None, wrap_cols=(), font=8.5):
        story.append(Paragraph(escape(ascii_txt(title)), s_h))
        story.append(tbl(rows, header, widths or kv, wrap_cols, font))

    fa = feed_analysis()
    verdict = {"ok": "ALL CHECKS PASSED", "warn": "PASSED WITH WARNINGS", "bad": "NOT VALID - RED CAUTIONS"}[status]
    m1 = d["m1"] if d else None
    section("1. Project & Verdict", [
        ["Project", str(project)], ["Client", g("pi_client", "")], ["Location", g("pi_location", "")],
        ["Prepared by", g("pi_engineer", "")], ["Project number / revision", f"{g('pi_number', '')} / {g('pi_revision', '0')}"],
        ["Water type", g("water_type", "")], ["RO passes", str(d["passes"]) if d else "-"],
        ["Membrane (pass 1)", f"{m1['vendor']} {m1['model']}" if m1 else "none"],
        ["Design verdict", verdict]])
    ion_rows = [[r["ion"], fmt(r["mg"], 3), fmt(r["caco3"], 3)] for r in fa["rows"] if r["mg"] > 0]
    section("2. Feed Water", [
        ["Temperature / pH", f"{fmt(fa['t'], 1)} C / {fmt(fa['ph'], 2)}"], ["TDS", fmt(fa["tds"], 1, "mg/L")],
        ["Conductivity at 25 C", fmt(fa["cond"], 1, "uS/cm")], ["Hardness / alkalinity", f"{fmt(fa['hardness'], 1)} / {fmt(fa['alk'], 1)} mg/L CaCO3"],
        ["Osmotic pressure", f"{fmt(fa['osm_bar'], 2)} bar ({fmt(fa['osm_bar'] * PSI, 1)} psi)"],
        ["CO2 (calculated)", fmt(fa["c"]["co2"], 2, "mg/L")], ["LSI (feed)", fmt(fa["lsi"], 2)],
        ["Charge balance", f"{fmt(fa['cbe'], 1)} %"]])
    story.append(Spacer(1, 6))
    story.append(tbl(ion_rows or [["-", "-", "-"]], ["Ion", "mg/L", "mg/L as CaCO3"], [W * 0.34, W * 0.33, W * 0.33]))

    if d:
        pl = d["pl"]
        header = ["Parameter"] + [f"Pass {e['n']}" for e in pl]

        def per(label, fn):
            return [label] + [fn(e) for e in pl]
        rows = [
            per("Membrane", lambda e: f"{e['mem']['vendor']} {e['mem']['model']}"),
            per("Feed pH", lambda e: fmt(e["ph_feed"], 2)),
            per("Recovery (%)", lambda e: fmt(e["calc"]["y"] * 100, 1)),
            per("Feed flow (m3/h | gpm)", lambda e: f"{fmt(e['calc']['f_m3h'], 2)} | {fmt(e['calc']['f'], 1)}"),
            per("Permeate flow (m3/h | gpm)", lambda e: f"{fmt(e['calc']['p_m3h'], 2)} | {fmt(e['calc']['p'], 1)}"),
            per("Concentrate flow (m3/h | gpm)", lambda e: f"{fmt(e['calc']['c_m3h'], 2)} | {fmt(e['calc']['c'], 1)}"),
            per("Average flux (gfd)", lambda e: fmt(e["calc"]["flux"], 1)),
            per("Elements / vessels", lambda e: f"{e['calc']['n_el']} / {e['calc']['n_vessels']}"),
            per("Membrane area (ft2)", lambda e: fmt(e["calc"]["area"], 0)),
            per("Fouling factor / TCF", lambda e: f"{fmt(e['calc']['ff'], 3)} / {fmt(e['calc']['tcf'], 3)}"),
            per("Average NDP (psi)", lambda e: fmt(e["calc"]["ndp"], 1)),
            per("Feed pressure (psi)", lambda e: fmt(e["calc"]["pf"], 1)),
            per("Pumping power (kW)", lambda e: fmt(e["calc"]["kw"], 1))]
        pad = [""] * (len(pl) - 1)
        rows += [["Plant product flow", f"{fmt(d['q'], 2)} m3/h"] + pad,
                 ["Raw feed flow / overall recovery", f"{fmt(d['raw'], 2)} m3/h / {fmt(d['overall_rec'], 1)} %"] + pad,
                 ["Total pumping power", fmt(d["power_kw"], 1, "kW")] + pad,
                 ["Specific energy", f"{fmt(d['spec_kwh_kgal'], 2)} kWh/kgal ({fmt(d['spec_kwh_m3'], 2)} kWh/m3)"] + pad]
        section("3. System Design Summary", rows, header, [W * 0.30] + [W * 0.70 / len(pl)] * len(pl),
                wrap_cols=tuple(range(1, len(pl) + 1)), font=8 if len(pl) < 3 else 7)
        story.append(Paragraph("4. Stage Details", s_h))
        for e in d["pl"]:
            n, pdx = e["n"], e["calc"]
            story.append(tbl([[f"{r['stage']}", f"{r['vessels']} x {r['elements']}", fmt(r["feed"], 1), fmt(r["perm"], 1), fmt(r["conc"], 1),
                               fmt(r["feed_v"], 1), fmt(r["conc_v"], 1), fmt(r["lead_rec"], 1), fmt(r["dp_stage"], 1), fmt(r["p_in"], 0)]
                              for r in pdx["rows"]],
                             [f"Pass {n} stage", "Vessels x el.", "Feed gpm", "Perm gpm", "Conc gpm", "Feed/vessel", "Conc/vessel", "Lead rec %", "dP psi", "Inlet psi"],
                             [W * 0.12, W * 0.11, W * 0.09, W * 0.09, W * 0.09, W * 0.11, W * 0.11, W * 0.10, W * 0.09, W * 0.09], font=7.5))
            story.append(Spacer(1, 5))
        story.append(Paragraph("5. Design Cautions", s_h))
        icon = {"ok": "OK", "warn": "WARNING", "bad": "FAIL", "info": "INFO"}
        story.append(tbl([[icon[c["level"]], c["text"]] for c in checks], ["Result", "Check"], [W * 0.14, W * 0.86], wrap_cols=(1,)))

        cp = chemical_program(d)
        story.append(PageBreak())
        crow = [[r["name"], r["point"], fmt(r["dose"], 2), fmt(r["flow"], 1), fmt(r["kg_h"], 3), f"{fmt(r['conc'], 0)}% / {fmt(r['sg'], 2)}",
                 fmt(r["sol_kg_h"], 3), fmt(r["l_h"], 2), fmt(r["kg_day"], 1), fmt(r["cost_day"], 0)] for r in cp["rows"] if r["dose"] > 0]
        story.append(Paragraph("6. Chemical Requirements", s_h))
        story.append(tbl(crow or [["-"] * 10], ["Chemical", "Point", "Dose mg/L", "Flow m3/h", "kg/h 100%", "Conc / SG", "Soln kg/h", "L/h", "kg/day 100%", "Cost/day"],
                         [W * 0.19, W * 0.15, W * 0.08, W * 0.08, W * 0.09, W * 0.10, W * 0.08, W * 0.07, W * 0.09, W * 0.07], wrap_cols=(0, 1), font=7))
        story.append(Spacer(1, 4))
        story.append(P(f"Antiscalant: {ss.get('as_product', '')} - recommended {fmt(cp['antiscalant_rec'], 2)} mg/L, applied {fmt(cp['antiscalant_dose'], 2)} mg/L. "
                       f"Chemical cost: {fmt(cp['cost_day'], 0)} per day ({fmt(cp['cost_m3'], 3)} per m3 of product).", s_small))
        story.append(Paragraph("7. Concentrate Scaling Indicators", s_h))
        story.append(tbl([[k, fmt(v, 1) + " %"] for k, v in d["sat_conc"].items()] + [["LSI (concentrate)", fmt(d["lsi_conc"], 2)], ["Concentration factor", fmt(d["cf"], 2)]],
                         ["Indicator", "Value"], [W * 0.5, W * 0.5]))
        qt = quality_table(d)
        story.append(PageBreak())
        eff = effluent_summary(d)
        eq_, ef = eff["q"], eff
        section("8. Treated Water after RO (Product & Concentrate)", [
            ["Raw feed flow", fmt(ef["flow_raw"], 2, "m3/h")], ["Product (permeate) flow", fmt(ef["flow_prod"], 2, "m3/h")],
            ["Concentrate (reject) flow", fmt(ef["flow_conc"], 2, "m3/h")], ["Overall recovery", fmt(ef["rec"], 1, "%")],
            ["Product TDS / pH", f"{fmt(eq_['prod']['tds'], 2)} mg/L / {fmt(eq_['prod']['ph'], 2)}"],
            ["Product conductivity", fmt(eq_["prod"]["cond"], 2, "uS/cm")], ["TDS rejection", fmt(ef["tds_rej"], 2, "%")],
            ["Concentrate TDS / pH", f"{fmt(eq_['conc']['tds'], 1)} mg/L / {fmt(eq_['conc']['ph'], 2)}"],
            ["Concentrate osmotic pressure", fmt(ef["osm_conc_psi"], 1, "psi")], ["Concentrate LSI", fmt(ef["lsi_conc"], 2)]])
        story.append(Spacer(1, 6))
        eff_rows = effluent_rows(eff)
        story.append(tbl([[r["param"], r["unit"], fmt(r["raw"], 3), fmt(r["prod"], 3), "-" if r["rej"] is None else fmt(r["rej"], 2),
                           fmt(r["conc"], 3)] for r in eff_rows],
                         ["Parameter", "Unit", "Raw water", "RO product", "Rejection %", "Concentrate"],
                         [W * 0.20, W * 0.17, W * 0.16, W * 0.16, W * 0.15, W * 0.16], font=7.5))
        if ef["post"]:
            story.append(Spacer(1, 4))
            story.append(P(f"After post-treatment: pH {fmt(ef['post']['ph'], 2)}, TDS {fmt(ef['post']['tds'], 2)} mg/L, alkalinity "
                           f"{fmt(ef['post']['alk'], 1)} mg/L CaCO3, hardness {fmt(ef['post']['hardness'], 1)} mg/L CaCO3, LSI {fmt(ef['post']['lsi'], 2)}.", s_small))
        story.append(PageBreak())
        story.append(Paragraph("9. Water Quality by Stream (mg/L)", s_h))
        def short_name(c):
            return re.sub(r"Pass (\d)", r"P\1", str(c)).replace("permeate", "perm").replace("concentrate", "conc").replace("Raw water", "Raw")
        data_cols = list(qt.columns[1:])
        for ci in range(0, len(data_cols), 7):             # at most 7 stream columns per table so that 3-4 pass designs stay readable
            chunk = ["Parameter"] + data_cols[ci:ci + 7]
            story.append(tbl([[str(x) for x in r] for r in qt[chunk].values.tolist()], [short_name(c) for c in chunk],
                             [W * 0.14] + [W * 0.86 / (len(chunk) - 1)] * (len(chunk) - 1), font=7))
            story.append(Spacer(1, 5))
        pt = post_treatment(d)
        story.append(Paragraph("10. Product Water After Post-Treatment", s_h))
        story.append(tbl([["pH", fmt(pt["ph"], 2)], ["TDS", fmt(pt["tds"], 2, "mg/L")], ["Alkalinity", fmt(pt["alk"], 1, "mg/L CaCO3")],
                          ["Hardness", fmt(pt["hardness"], 1, "mg/L CaCO3")], ["LSI", fmt(pt["lsi"], 2)]], None, kv))
    story.append(Paragraph("11. Basis & Limitations", s_h))
    notes = ["Flux = permeate / membrane area; fouling factor = (1 - flux decline)^age; feed pressure = NDP + osmotic pressure (log-mean) + permeate pressure + half the vessel dP.",
             "Pump power = flow x pressure / (1714 x pump x motor x VFD efficiency); specific energy per kgal of plant product (IMSDesign method).",
             "Chemical doses come from an alkalinity balance with total carbonate conserved; CO2 passes the membrane with a passage of 0.88 (calibrated to IMSDesign).",
             "Membrane permeability and element pressure drop are type-typical unless a membrane is marked calibrated; vendor guideline limits are typical 8-inch values.",
             "Concentrate = mass balance of the stage concentrates (the pass-2 concentrate is added when it is not recycled); product values are salt passage x log-mean feed-concentrate concentration.",
             "This is an estimating tool. Confirm the final design with the membrane manufacturer's projection software (IMSDesign, WAVE, LG Q+, Toray DS2, LewaPlus)."]
    for n_ in notes:
        story.append(Paragraph("- " + escape(ascii_txt(n_)), s_small))

    def decor(canvas, doc):
        canvas.saveState()
        canvas.setStrokeColor(BLUE)
        canvas.setLineWidth(1.2)
        canvas.line(18 * mm, A4[1] - 15 * mm, A4[0] - 18 * mm, A4[1] - 15 * mm)
        canvas.setFont("Helvetica-Bold", 9)
        canvas.setFillColor(NAVY)
        canvas.drawString(18 * mm, A4[1] - 12 * mm, APP_TITLE)
        canvas.setFont("Helvetica", 8)
        canvas.setFillColor(colors.grey)
        canvas.drawRightString(A4[0] - 18 * mm, A4[1] - 12 * mm, ascii_txt(str(project))[:60])
        canvas.drawString(18 * mm, 10 * mm, f"Generated {now}")
        canvas.drawRightString(A4[0] - 18 * mm, 10 * mm, f"Page {doc.page}")
        canvas.restoreState()

    buf = BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4, leftMargin=18 * mm, rightMargin=18 * mm, topMargin=22 * mm, bottomMargin=18 * mm,
                            title=f"{APP_TITLE} - {project}", author="HSKH")
    doc.build(story, onFirstPage=decor, onLaterPages=decor)
    return buf.getvalue()
# <<< PURE-END


# =====================================================
# LOOK & FEEL  (themes: page / sidebar gradient + box colours)
# =====================================================
THEMES = {
    # bluish gradient page + sidebar, white boxes, white tabs, black text
    "sky blue": {
        "__BG__": "linear-gradient(135deg, #EAF3FC 0%, #BFD9F2 32%, #8DBBE8 68%, #5E9BD8 100%)", "__HTXT__": "#000000", "__HSUB__": "#1F2D3A",
        "__HBG__": "rgba(234,243,252,.96)", "__PAGEH__": "#000000", "__CHIPBG__": "#FFFFFF", "__CHIPBD__": "#8FB4D8", "__CHIPTX__": "#000000",
        "__ACC__": "#2F86C0", "__ACCD__": "#1D6397", "__TXT__": "#000000", "__TXT2__": "#111111", "__SUB__": "#2B2B2B",
        "__CARDBG__": "#FFFFFF", "__CARDBD__": "#A9C4DE", "__TILEBG__": "#FFFFFF", "__TILEBD__": "#B9CFE4",
        "__SHADOW__": "rgba(20,60,110,.28)",
        "__SIDE__": "linear-gradient(135deg, #0A1F3D 0%, #123A6B 45%, #0B2447 100%)", "__NAVBG__": "#FFFFFF", "__NAVBD__": "#9DBBD8", "__SBBOX__": "rgba(255,255,255,.92)", "__SBBOXBD__": "#9DBBD8", "__SBBG__": "linear-gradient(180deg, #14407A 0%, #0A1F3D 100%)", "__SBTX__": "#000000", "__SBHV__": "#E3F0FC",
        "__NAVACTBG__": "#FFFFFF", "__NAVACTTX__": "#000000", "__NAVBAR__": "#1D6397", "__BTN1__": "#3E9BD4", "__BTN2__": "#2478AD",
    },
    # metallic bluish-grey page + sidebar (one seamless gradient), white boxes
    "metal blue": {
        "__BG__": "linear-gradient(135deg, #2B3A4B 0%, #6F869C 16%, #3C4D61 32%, #7A90A6 50%, #475A70 68%, #6A8096 84%, #2B3A4B 100%)", "__HTXT__": "#F3F7FB", "__HSUB__": "#C3D0DD",
        "__HBG__": "rgba(40,54,70,.95)", "__PAGEH__": "#F3F7FB", "__CHIPBG__": "#2E3F52", "__CHIPBD__": "#7790A8", "__CHIPTX__": "#EEF3F8",
        "__ACC__": "#2F86C0", "__ACCD__": "#1D6397", "__TXT__": "#16384F", "__TXT2__": "#1F4A66", "__SUB__": "#5A7389",
        "__CARDBG__": "#FFFFFF", "__CARDBD__": "#B8C8D8", "__TILEBG__": "#FFFFFF", "__TILEBD__": "#CBD8E4",
        "__SHADOW__": "rgba(5,15,30,.5)",
        "__NAVBG__": "rgba(255,255,255,.08)", "__NAVBD__": "rgba(255,255,255,.22)", "__SBBOX__": "rgba(255,255,255,.12)", "__SBBOXBD__": "rgba(255,255,255,.28)", "__SBBG__": "transparent", "__SBTX__": "#F2F6FA", "__SBHV__": "rgba(255,255,255,.18)",
        "__NAVACTBG__": "#EEF3F8", "__NAVACTTX__": "#16384F", "__NAVBAR__": "#2F86C0", "__BTN1__": "#3E9BD4", "__BTN2__": "#2478AD",
    },
    # light grey -> light blue page gradient, white boxes, light blue sidebar with blue active tab
    "light blue": {
        "__BG__": "linear-gradient(135deg, #ECEFF2 0%, #DCE6EE 40%, #BFD9EE 100%)", "__HTXT__": "#16384F", "__HSUB__": "#5A7389",
        "__HBG__": "rgba(240,244,248,.96)", "__PAGEH__": "#16384F", "__CHIPBG__": "#FFFFFF", "__CHIPBD__": "#A9C2D6", "__CHIPTX__": "#16384F",
        "__ACC__": "#2F86C0", "__ACCD__": "#1D6397", "__TXT__": "#16384F", "__TXT2__": "#1F4A66", "__SUB__": "#5A7389",
        "__CARDBG__": "#FFFFFF", "__CARDBD__": "#C9D6E2", "__TILEBG__": "#FFFFFF", "__TILEBD__": "#D3DEE8",
        "__SHADOW__": "rgba(30,60,90,.18)",
        "__NAVBG__": "rgba(255,255,255,.65)", "__NAVBD__": "rgba(47,134,192,.25)", "__SBBOX__": "rgba(255,255,255,.75)", "__SBBOXBD__": "rgba(47,134,192,.30)",
        "__SBBG__": "linear-gradient(180deg, #E4EAF0 0%, #C9DDEE 100%)", "__SBTX__": "#16384F", "__SBHV__": "rgba(47,134,192,.15)",
        "__NAVACTBG__": "#2F86C0", "__NAVACTTX__": "#FFFFFF", "__NAVBAR__": "#16384F", "__BTN1__": "#3E9BD4", "__BTN2__": "#2478AD",
    },
    # metallic grey page + sidebar (one seamless gradient), light grey data boxes
    "grey": {
        "__BG__": "linear-gradient(135deg, #2A2E33 0%, #6B7279 20%, #3C4046 38%, #7A8087 56%, #484D54 76%, #2A2E33 100%)", "__HTXT__": "#F4F5F7", "__HSUB__": "#B9BEC6",
        "__HBG__": "rgba(44,48,53,.95)", "__PAGEH__": "#F4F5F7", "__CHIPBG__": "#2E3238", "__CHIPBD__": "#6A707A", "__CHIPTX__": "#EEF0F2",
        "__ACC__": "#2F86C0", "__ACCD__": "#1D6397", "__TXT__": "#23272D", "__TXT2__": "#2F353C", "__SUB__": "#5A616B",
        "__CARDBG__": "linear-gradient(135deg, #F6F7F8 0%, #E3E6EA 100%)", "__CARDBD__": "#B5BAC2", "__TILEBG__": "#FBFBFC", "__TILEBD__": "#CBCFD5",
        "__SHADOW__": "rgba(0,0,0,.45)",
        "__NAVBG__": "rgba(255,255,255,.07)", "__NAVBD__": "rgba(255,255,255,.18)", "__SBBOX__": "rgba(255,255,255,.10)", "__SBBOXBD__": "rgba(255,255,255,.25)", "__SBBG__": "transparent", "__SBTX__": "#F2F3F5", "__SBHV__": "rgba(255,255,255,.16)",
        "__NAVACTBG__": "#EDEFF1", "__NAVACTTX__": "#23272D", "__NAVBAR__": "#2F86C0", "__BTN1__": "#3E9BD4", "__BTN2__": "#2478AD",
    },
    # light grey -> light green page, light blue data boxes, dark grey-green tab rail
    "grey green": {
        "__BG__": "linear-gradient(135deg, #E8EAEC 0%, #D3E0D7 45%, #B9DDBB 100%)", "__HTXT__": "#24402C", "__HSUB__": "#5C7565",
        "__HBG__": "rgba(236,240,238,.96)", "__PAGEH__": "#24402C", "__CHIPBG__": "#FFFFFF", "__CHIPBD__": "#9DB8A5", "__CHIPTX__": "#24402C",
        "__ACC__": "#2F86C0", "__ACCD__": "#1D6397", "__TXT__": "#16384F", "__TXT2__": "#1F4A66", "__SUB__": "#4C6F86",
        "__CARDBG__": "linear-gradient(135deg, #EAF5FD 0%, #D6EBF9 100%)", "__CARDBD__": "#8FBFE0", "__TILEBG__": "#F5FAFE", "__TILEBD__": "#B7D5EA",
        "__SHADOW__": "rgba(30,60,50,.22)",
        "__NAVBG__": "rgba(255,255,255,.07)", "__NAVBD__": "rgba(255,255,255,.16)", "__SBBOX__": "rgba(255,255,255,.12)", "__SBBOXBD__": "rgba(255,255,255,.25)", "__SBBG__": "linear-gradient(180deg, #4B6455 0%, #2F4439 100%)", "__SBTX__": "#F1F6F2", "__SBHV__": "rgba(255,255,255,.18)",
        "__NAVACTBG__": "#DCEEFA", "__NAVACTTX__": "#16384F", "__NAVBAR__": "#4FA66A", "__BTN1__": "#3E9BD4", "__BTN2__": "#2478AD",
    },
    # light-brown page, light-green data boxes, dark-brown vertical tab rail
    "light brown": {
        "__BG__": "linear-gradient(135deg, #F1E7D6 0%, #E2D0B3 50%, #D3BB95 100%)", "__HTXT__": "#4A3320", "__HSUB__": "#7C634A",
        "__HBG__": "rgba(241,231,214,.96)", "__PAGEH__": "#4A3320", "__CHIPBG__": "#FBF6EC", "__CHIPBD__": "#C3A682", "__CHIPTX__": "#4A3320",
        "__ACC__": "#5E9E4A", "__ACCD__": "#437A33", "__TXT__": "#2A4426", "__TXT2__": "#36573A", "__SUB__": "#5D7856",
        "__CARDBG__": "#E3F1DC", "__CARDBD__": "#A6CB9A", "__TILEBG__": "#F4FAF0", "__TILEBD__": "#BAD6AF", "__SHADOW__": "rgba(74,51,32,.22)",
        "__NAVBG__": "rgba(255,255,255,.07)", "__NAVBD__": "rgba(255,255,255,.16)", "__SBBOX__": "rgba(255,255,255,.12)", "__SBBOXBD__": "rgba(255,255,255,.25)", "__SBBG__": "linear-gradient(180deg, #80623F 0%, #5B4229 100%)", "__SBTX__": "#F7EFE0", "__SBHV__": "rgba(255,255,255,.18)",
        "__NAVACTBG__": "#E3F1DC", "__NAVACTTX__": "#2A4426", "__NAVBAR__": "#5E9E4A", "__BTN1__": "#74B35C", "__BTN2__": "#4F8A3C",
    },
    # dark alternative
    "charcoal": {
        "__BG__": "linear-gradient(135deg, #1B1F24 0%, #2B313A 50%, #434B56 100%)", "__HTXT__": "#F4F7FA", "__HSUB__": "#B9C5D1",
        "__HBG__": "rgba(27,31,36,.96)", "__PAGEH__": "#F4F7FA", "__CHIPBG__": "#2E343C", "__CHIPBD__": "#5C6874", "__CHIPTX__": "#E8EDF2",
        "__ACC__": "#0E9AC9", "__ACCD__": "#0A6E92", "__TXT__": "#14283A", "__TXT2__": "#2A4A63", "__SUB__": "#58708A",
        "__CARDBG__": "#FFFFFF", "__CARDBD__": "#B7C7D6", "__TILEBG__": "#F4F8FB", "__TILEBD__": "#C6D6E2", "__SHADOW__": "rgba(0,0,0,.30)",
        "__NAVBG__": "rgba(255,255,255,.07)", "__NAVBD__": "rgba(255,255,255,.16)", "__SBBOX__": "rgba(255,255,255,.12)", "__SBBOXBD__": "rgba(255,255,255,.25)", "__SBBG__": "linear-gradient(180deg, #2B313A 0%, #1B1F24 100%)", "__SBTX__": "#EAF0F5", "__SBHV__": "rgba(255,255,255,.14)",
        "__NAVACTBG__": "#FFFFFF", "__NAVACTTX__": "#14283A", "__NAVBAR__": "#0E9AC9", "__BTN1__": "#1C95C2", "__BTN2__": "#0E7FA8",
    },
}


def apply_layout_css():
    css = """
    <style>
    :root { color-scheme: light; }
    #MainMenu, footer { visibility: hidden; }
    [data-testid="stHeader"] { background: transparent; }
    [data-testid="stToolbar"], [data-testid="stDecoration"] { visibility: hidden; }
    [data-testid="stElementContainer"]:has(style), .element-container:has(style) { display: none !important; }

    html, body, .stApp, [data-testid="stAppViewContainer"] { background: __SIDE__ !important; background-attachment: fixed !important; min-height: 100vh; }
    [data-testid="stMain"], [data-testid="stBottom"] > div { background: transparent !important; }
    .block-container { max-width: __W__vw !important; padding: 0 12px 3rem 12px !important; background: __BG__; background-attachment: fixed; min-height: 100vh; box-shadow: 0 0 28px rgba(0,0,0,.55); margin-top: 0 !important; }
    @media (max-width: 1100px) { .block-container { max-width: 96vw !important; } }
    .mdw { padding-bottom: 1rem; }

    /* ---------- title band (stays on top while scrolling) ---------- */
    [data-testid="stElementContainer"]:has(.hdr), .element-container:has(.hdr) {
        position: sticky; top: 0; z-index: 999; background: __HBG__; backdrop-filter: blur(6px);
        box-shadow: 0 5px 12px __SHADOW__; border-radius: 0 0 12px 12px; padding: 8px 10px 0 10px; }
    .hdr { display:flex; justify-content:space-between; align-items:flex-end; gap:16px; padding: 6px 4px 12px 4px; border-bottom: 3px solid __ACC__; }
    .hdr-title { font-size: 21px; font-weight: 900; color:__HTXT__; letter-spacing:.5px; line-height:1.05; }
    .hdr-sub { color:__HSUB__; font-size:11px; letter-spacing:2.5px; text-transform:uppercase; margin-top:4px; font-weight:700; }
    .hdr-right { display:flex; flex-direction:column; align-items:flex-end; gap:6px; }
    .chip { background:__CHIPBG__; border:1px solid __CHIPBD__; color:__CHIPTX__; padding:4px 12px; border-radius:999px; font-size:12.5px; font-weight:700; white-space:nowrap; }
    .chip.ok { border-color:__ACC__; }
    .chip.dgood { background:#E6F6EC; border-color:#1B8F5A; color:#1B4D34; }
    .chip.dwarn { background:#FFF7E8; border-color:#E08A00; color:#6B4A00; }
    .chip.dbad  { background:#FDECEC; border-color:#C62828; color:#7A1F1F; }
    .page-h { text-shadow:0 1px 2px rgba(255,255,255,.5); color:__PAGEH__; font-size:18px; font-weight:800; margin: 4px 2px 0 2px; letter-spacing:.3px; }

    /* ---------- data boxes ---------- */
    [class*="st-key-card_"] { background:__CARDBG__; border:1px solid __CARDBD__; border-left:6px solid __ACC__; border-radius:12px;
        padding: 7px 11px 8px 10px; box-shadow: 0 3px 10px __SHADOW__; margin-bottom: .2rem; gap: .3rem; border-radius:9px; }
    .card-title { font-weight:800; color:__TXT__; font-size:13px; letter-spacing:.3px; line-height:1.3; border-bottom:2px dashed __ACC__; padding-bottom:3px; }
    .sub { font-weight:800; color:__ACCD__; font-size:11px; text-transform:uppercase; letter-spacing:.7px; line-height:1.3; margin-top:4px; }
    .pmeta { color:__SUB__; font-size:12px; line-height:1.45; }
    .lhead { font-weight:800; color:__ACCD__; font-size:10.5px; text-transform:uppercase; letter-spacing:.6px; }

    .tiles { display:grid; grid-template-columns: repeat(auto-fill, minmax(118px, 1fr)); gap:5px; }
    .tile { background:__TILEBG__; border:1px solid __TILEBD__; border-bottom:3px solid __ACC__; border-radius:6px; padding:3px 7px; min-width:0; min-height:36px; }
    .tile .t-l { font-size:9px; color:__SUB__; text-transform:uppercase; letter-spacing:.5px; line-height:1.3; }
    .tile .t-v { font-size:12px; font-weight:800; color:__TXT__; line-height:1.3; overflow-wrap:anywhere; }
    .tile.warn { border-bottom-color:#E08A00; background:#FFF7E8; }
    .tile.bad  { border-bottom-color:#C62828; background:#FDECEC; }
    .tile.good { border-bottom-color:#1B8F5A; background:#EEF8F1; }

    .chk { padding:3px 8px; border-left:4px solid; border-radius:5px; margin-bottom:3px; font-size:11.5px; line-height:1.4; }
    .chk.ok   { background:#F4FAF0; border-color:#1B8F5A; color:#1B4D34; }
    .chk.warn { background:#FFF7E8; border-color:#E08A00; color:#6B4A00; }
    .chk.bad  { background:#FDECEC; border-color:#C62828; color:#7A1F1F; font-weight:700; }
    .chk.info { background:#EEF4FA; border-color:#5B8DB8; color:#1F3F5C; }
    .eq { display:inline-block; margin-top:.45rem; font-size:12.5px; color:__SUB__; }

    [data-testid="stWidgetLabel"] p { font-size:11px; font-weight:600; color:__TXT2__ !important; margin-bottom:0; }
    [data-testid="stNumberInput"] input, [data-testid="stTextInput"] input { font-size:12px; padding:.15rem .4rem; }
    [data-testid="stNumberInput"] > div > div, [data-testid="stTextInput"] > div > div { min-height: 1.7rem; }
    [data-testid="stSelectbox"] div[data-baseweb="select"] > div { min-height:1.7rem; font-size:12px; }
    [data-testid="stAlert"] { padding: .25rem .6rem; font-size: 11.5px; }
    .stCaption, [data-testid="stCaptionContainer"] { color:__SUB__ !important; }
    [data-testid="stDataFrame"], [data-testid="stDataEditor"] { border:1px solid __TILEBD__; border-radius:8px; }

    .stButton button, .stDownloadButton button { background: linear-gradient(180deg,__BTN1__,__BTN2__); color:#fff; border:0;
        border-radius:7px; font-weight:700; width:100%; padding:.2rem .5rem; font-size:12px; }
    .stButton button p, .stDownloadButton button p { color:#fff; }
    .stButton button:hover, .stDownloadButton button:hover { background:__ACCD__; color:#fff; }
    .stButton button:disabled { background:#A9B5A4; color:#fff; }

    /* ---------- vertical tab rail (left) ---------- */
    [data-testid="stSidebar"] { background: __SBBG__ !important; border-right: 1px solid rgba(0,0,0,.18); }
    [data-testid="stSidebar"] > div, [data-testid="stSidebarContent"], [data-testid="stSidebarHeader"] { background: transparent !important; }
    [data-testid="stSidebar"] * { color:__SBTX__; }
    .sb-brand { font-size:24px; font-weight:900; letter-spacing:.5px; line-height:1.1; padding:6px 2px 12px 2px; border-bottom:2px solid __ACC__; }
    .sb-brand small { display:block; font-size:11px; font-weight:700; letter-spacing:2.5px; opacity:.8; text-transform:uppercase; margin-top:3px; }
    .sb-brand, .sb-brand *, .sb-h { color:#F2F4F6 !important; }
    .sb-h { font-size:11px; letter-spacing:2px; font-weight:800; opacity:.75; margin:10px 0 0 2px; text-transform:uppercase; }
    .sb-status { font-size:12px; background:__SBBOX__; border:1px solid __SBBOXBD__; border-radius:8px; padding:7px 10px; line-height:1.5; }
    .st-key-sidenav button { justify-content:flex-start; text-align:left; font-size:13px; padding:.4rem .6rem; border-radius:8px; margin-bottom:.05rem; }
    .st-key-sidenav button[kind="secondary"], .st-key-sidenav button[data-testid="stBaseButton-secondary"] {
        background:__NAVBG__ !important; border:1px solid __NAVBD__ !important; border-left:5px solid transparent !important; box-shadow:none !important; }
    .st-key-sidenav button[kind="secondary"] *, .st-key-sidenav button[data-testid="stBaseButton-secondary"] * { color:__SBTX__ !important; font-weight:600 !important; }
    .st-key-sidenav button[kind="secondary"]:hover, .st-key-sidenav button[data-testid="stBaseButton-secondary"]:hover {
        background:__SBHV__ !important; border-left-color:__ACC__ !important; }
    .st-key-sidenav button[kind="primary"], .st-key-sidenav button[data-testid="stBaseButton-primary"] {
        background:__NAVACTBG__ !important; border:1px solid __NAVACTBG__ !important; border-left:5px solid __NAVBAR__ !important; box-shadow:0 3px 8px rgba(0,0,0,.3) !important; outline:2px solid __NAVBAR__; }
    .st-key-sidenav button[kind="primary"] *, .st-key-sidenav button[data-testid="stBaseButton-primary"] * { color:__NAVACTTX__ !important; font-weight:800 !important; }

    /* ---------- inputs stay white with dark text (even if Streamlit is in dark mode) ---------- */
    [class*="st-key-card_"] p, [class*="st-key-card_"] li, [class*="st-key-card_"] label,
    [class*="st-key-card_"] [data-testid="stMarkdownContainer"], [class*="st-key-card_"] [data-testid="stCheckbox"] span,
    [class*="st-key-card_"] [data-testid="stRadio"] span { color:__TXT__ !important; }
    [data-testid="stTextInputRootElement"], [data-testid="stNumberInputContainer"], [data-testid="stTextAreaRootElement"],
    div[data-baseweb="input"], div[data-baseweb="textarea"], div[data-baseweb="select"] > div {
        background:#FFFFFF !important; background-color:#FFFFFF !important; border:1px solid #7D848E !important; border-radius:6px !important; }
    div[data-baseweb="base-input"], div[data-baseweb="base-input"] > div { background:transparent !important; background-color:transparent !important; }
    input, textarea { background-color:#FFFFFF !important; color:#111111 !important; -webkit-text-fill-color:#111111 !important; caret-color:#111111; }
    div[data-baseweb="select"] div, div[data-baseweb="select"] span, div[data-baseweb="select"] input {
        background-color:#FFFFFF !important; color:#111111 !important; -webkit-text-fill-color:#111111 !important; }
    div[data-baseweb="select"] svg { fill:#111111 !important; }
    input:disabled, textarea:disabled { background-color:#E8EAED !important; -webkit-text-fill-color:#555555 !important; color:#555555 !important; }
    div[data-baseweb="input"]:has(input:disabled), [data-testid="stNumberInputContainer"]:has(input:disabled) { background:#E8EAED !important; background-color:#E8EAED !important; }
    [data-testid="stNumberInput"] button { background-color:#FFFFFF !important; color:#111111 !important; border-color:#7D848E !important; }
    [data-testid="stNumberInput"] button svg { fill:#111111 !important; }
    [data-testid="stFileUploaderDropzone"] { background-color:#FFFFFF !important; border:1px dashed #7D848E !important; }
    [data-testid="stFileUploaderDropzone"] * { color:#111111 !important; }
    </style>
    """
    tokens = {"__W__": str(APP_WIDTH_VW)}
    tokens.update(THEMES.get(THEME, THEMES["sky blue"]))
    tokens.setdefault("__SIDE__", tokens["__BG__"])      # colour of the page margins left / right of the content column
    for k, v in tokens.items():
        css = css.replace(k, v)
    st.markdown(css, unsafe_allow_html=True)


apply_layout_css()

# =====================================================
# UI HELPERS
# =====================================================
_CARD_N = [0]


def md(html):
    st.markdown(f'<div class="mdw">{html}</div>', unsafe_allow_html=True)


@contextmanager
def card(title=None, icon=""):
    _CARD_N[0] += 1
    try:
        box = st.container(key=f"card_{_CARD_N[0]}")
    except TypeError:
        box = st.container()
    with box:
        if title:
            md(f'<div class="card-title">{icon} {hesc(title)}</div>')
        yield


def sub(text):
    md(f'<div class="sub">{hesc(text)}</div>')


def page_title(text):
    md(f'<div class="page-h">{hesc(text)}</div>')


def tiles(items):
    html = ['<div class="tiles">']
    for it in items:
        cls = f" {it[2]}" if len(it) > 2 else ""
        html.append(f'<div class="tile{cls}"><div class="t-l">{hesc(str(it[0]))}</div><div class="t-v">{hesc(str(it[1]))}</div></div>')
    html.append("</div>")
    md("".join(html))


def show_df(df, **kw):
    try:
        st.dataframe(df, width="stretch", **kw)
    except TypeError:
        st.dataframe(df, use_container_width=True, **kw)


def checklist(checks):
    icons = {"ok": "✅", "warn": "⚠️", "bad": "❌", "info": "ℹ️"}
    order = {"bad": 0, "warn": 1, "info": 2, "ok": 3}
    md("".join(f'<div class="chk {c["level"]}">{icons[c["level"]]} {hesc(c["text"])}</div>'
               for c in sorted(checks, key=lambda c: order[c["level"]])))


def status_banner(checks, title="Design check"):
    lvl = overall(checks)
    bad = [c for c in checks if c["level"] == "bad"]
    if lvl == "bad":
        st.error(f"❌ {title}: {len(bad)} red caution(s) - {bad[0]['text']}")
    elif lvl == "warn":
        st.warning(f"⚠️ {title}: acceptable, with warnings - see the list below.")
    else:
        st.success(f"✅ {title}: membrane selection, flux and flows are acceptable.")
    sig = (lvl, len(bad), bad[0]["text"] if bad else "")
    if ss.get("_chk_sig") != sig:
        ss["_chk_sig"] = sig
        try:
            st.toast({"bad": "❌ RO design has red cautions", "warn": "⚠️ RO design passed with warnings", "ok": "✅ RO design is OK"}[lvl])
        except Exception:
            pass


# =====================================================
# PROJECT FILES + AUTO-SAVE ENGINE
# =====================================================
if "_saved" not in ss:
    ss["_saved"] = {}
SAVED = ss["_saved"]


def _is_saved_key(k):
    return isinstance(k, str) and not k.startswith(NO_SAVE_PREFIX)


def _safe_name(name):
    s = re.sub(r"[^\w\- ]+", "", str(name)).strip().replace(" ", "_")
    return s or "Project"


def _default_project_name():
    return "RO_" + datetime.now().strftime("%Y%m%d_%H%M")


def collect_project():
    data = {k: v for k, v in SAVED.items() if _is_saved_key(k)}
    for k, v in ss.items():
        if _is_saved_key(k):
            data[k] = v
    clean = {}
    for k, v in data.items():
        try:
            json.dumps(v)
            clean[k] = v
        except (TypeError, ValueError):
            pass
    return clean


def project_json():
    body = collect_project()
    body["_meta"] = {"app": APP_TITLE, "version": 1, "saved_at": datetime.now().isoformat(timespec="seconds")}
    return json.dumps(body, indent=2, default=str)


def load_project_data(data, clear=True):
    if clear:
        for k in list(ss.keys()):
            if _is_saved_key(k):
                del ss[k]
        for k in [k for k in SAVED if _is_saved_key(k)]:
            del SAVED[k]
    for k, v in data.items():
        if _is_saved_key(k):
            ss[k] = v
            SAVED[k] = v


def project_path(name=None):
    n = _safe_name(name or ss.get("project_name") or _default_project_name())
    return PROJECT_DIR / n / f"{n}{PROJECT_EXT}"


def _write_last(rel):
    try:
        PROJECT_DIR.mkdir(parents=True, exist_ok=True)
        (PROJECT_DIR / ".last_project").write_text(rel, encoding="utf-8")
    except OSError:
        pass


def save_to_disk():
    try:
        path = project_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(project_json(), encoding="utf-8")
        _write_last(str(path.relative_to(PROJECT_DIR)).replace("\\", "/"))
        ss["_last_path"] = str(path)
        ss["_last_saved_at"] = datetime.now().strftime("%H:%M:%S")
        ss["_disk_error"] = ""
        return path
    except OSError as e:
        ss["_disk_error"] = str(e)
        return None


@st.cache_data(show_spinner=False)
def _project_meta(path_str, mtime):
    try:
        d = json.loads(Path(path_str).read_text(encoding="utf-8"))
    except Exception:
        return {}
    return {"name": d.get("project_name", ""), "client": d.get("pi_client", ""), "membrane": d.get("model1", ""),
            "flow": d.get("product_flow"), "passes": d.get("passes", 1), "water": d.get("water_type", "")}


def list_projects():
    out = []
    try:
        for p in PROJECT_DIR.glob(f"*/*{PROJECT_EXT}"):
            mt = p.stat().st_mtime
            meta = _project_meta(str(p), mt)
            out.append({"rel": str(p.relative_to(PROJECT_DIR)).replace("\\", "/"), "mtime": mt, "name": meta.get("name") or p.stem,
                        **{k: meta.get(k) for k in ("client", "membrane", "flow", "passes", "water")}})
    except OSError:
        return []
    return sorted(out, key=lambda x: x["mtime"], reverse=True)


def _ago(ts):
    s = max(0, datetime.now().timestamp() - ts)
    if s < 60:
        return "just now"
    if s < 3600:
        return f"{int(s // 60)} min ago"
    if s < 86400:
        return f"{int(s // 3600)} h ago"
    if s < 2592000:
        return f"{int(s // 86400)} days ago"
    return f"{int(s // 2592000)} months ago"


def _cb_new():
    load_project_data({}, clear=True)
    ss["project_name"] = SAVED["project_name"] = _default_project_name()
    ss["nav_main"] = MAIN_TABS[0]
    ss["_flash"] = ("success", "New project created - it gets its own folder automatically.")


def _cb_open_path(rel):
    try:
        load_project_data(json.loads((PROJECT_DIR / rel).read_text(encoding="utf-8")))
        if not ss.get("project_name"):
            ss["project_name"] = SAVED["project_name"] = Path(rel).stem
        _write_last(rel)
        ss["nav_main"] = MAIN_TABS[1]
        ss["_flash"] = ("success", f"Opened project: {rel}")
    except Exception as e:
        ss["_flash"] = ("error", f"Could not open project: {e}")


def _cb_upload():
    f = ss.get("ui_upload")
    if f is None:
        return
    try:
        load_project_data(json.loads(f.getvalue().decode("utf-8")))
        if not ss.get("project_name"):
            ss["project_name"] = SAVED["project_name"] = Path(f.name).stem
        ss["nav_main"] = MAIN_TABS[1]
        ss["_flash"] = ("success", f"Loaded project file: {f.name}")
    except Exception as e:
        ss["_flash"] = ("error", f"Invalid project file: {e}")


def _cb_example():
    for k, v in IMS_EXAMPLE.items():
        ss[k] = v
        SAVED[k] = v
    ss["_flash"] = ("success", "IMSDesign example loaded: NTPC11, ESPA2 MAX, two-pass, 209.95 gpm.")


def _cb_set(key, value):
    ss[key] = value
    SAVED[key] = value


if "_booted" not in ss:
    ss["_booted"] = True
    if AUTOLOAD_LAST:
        try:
            rel = (PROJECT_DIR / ".last_project").read_text(encoding="utf-8").strip()
            load_project_data(json.loads((PROJECT_DIR / rel).read_text(encoding="utf-8")), clear=False)
        except Exception:
            pass
for _k, _v in SAVED.items():
    if _k not in ss:
        ss[_k] = _v


# ---- widget helpers: values live in plain data keys; widgets use "w_<key>" and sync through on_change ----
def _sync(key, wkey):
    ss[key] = ss[wkey]
    SAVED[key] = ss[wkey]


def _stored(key, default):
    return ss[key] if key in ss else SAVED.get(key, default)


def _prepare(key, cur):
    wkey = "w_" + key
    ss[key] = cur
    SAVED[key] = cur
    ss[wkey] = cur
    return wkey


def w_number(label, key, default=0.0, **kw):
    cur = _stored(key, default)
    is_int = isinstance(default, int) and not isinstance(default, bool)
    try:
        cur = int(cur) if is_int else float(cur)
    except (TypeError, ValueError):
        cur = default
    if kw.get("min_value") is not None:
        cur = max(cur, type(cur)(kw["min_value"]))
    if kw.get("max_value") is not None:
        cur = min(cur, type(cur)(kw["max_value"]))
    wkey = _prepare(key, cur)
    return st.number_input(label, key=wkey, on_change=_sync, args=(key, wkey), **kw)


def _w(fn, label, key, default, *pos, **kw):
    wkey = _prepare(key, _stored(key, default))
    return fn(label, *pos, key=wkey, on_change=_sync, args=(key, wkey), **kw)


def _choice(fn, label, options, key, default, **kw):
    options = list(options) or ["-"]
    if default is None or default not in options:
        default = options[0]
    cur = _stored(key, default)
    if cur not in options:
        cur = default
    wkey = _prepare(key, cur)
    return fn(label, options, key=wkey, on_change=_sync, args=(key, wkey), **kw)


def w_select(label, options, key, default=None, **kw):
    return _choice(st.selectbox, label, options, key, default, **kw)


def w_radio(label, options, key, default=None, **kw):
    return _choice(st.radio, label, options, key, default, **kw)


def w_check(label, key, default=False, **kw):
    return _w(st.checkbox, label, key, default, **kw)


def w_text(label, key, default="", **kw):
    return _w(st.text_input, label, key, default, **kw)


def w_area(label, key, default="", **kw):
    return _w(st.text_area, label, key, default, **kw)


def w_unit_number(label, canon, default_canon, unit_key, units, **kw):
    unit = ss.get(unit_key) or next(iter(units))
    to_d, from_d = units.get(unit, next(iter(units.values())))
    cur = float(_stored(canon, default_canon))
    ss[canon] = SAVED[canon] = cur
    wkey = "w_" + canon
    ss[wkey] = float(round(to_d(cur), 6))

    def _cb():
        v = float(from_d(ss[wkey]))
        ss[canon] = SAVED[canon] = v

    return st.number_input(label, key=wkey, on_change=_cb, **kw)


FLOW_UNITS = {"m³/h": (lambda q: q, lambda v: v), "gpm": (lambda q: q * GPM, lambda v: v / GPM)}

for _k, _v in {"project_name": _default_project_name(), "ph": 7.0, "temp_c": 25.0, "water_type": "Municipal Water", "flow_unit": "m³/h",
               "pressure_unit": "psi", "passes": 1, "product_flow": 37.5, "p1_rec": 75.0, "p2_rec": 85.0, "recycle": True,
               "age1": 3.0, "decl1": 7.0, "sp1": 7.0, "age2": 3.0, "decl2": 3.0, "sp2": 5.0, "vendor1": "DuPont", "series1": "FilmTec BW",
               "model1": "BW30-400", "same2": True, "p1_stages": 3, "p2_stages": 2, "perm_pressure": 0.0, "target_tds": 10.0,
               "calc_co2": True, "p1_chem": "None", "p2_chem": "NaOH", "p2_ph": 8.2, "as_product": "Vitec 3000",
               "as_mode": "Recommended", "free_cl": 0.0, "smbs_mode": "Manual dose", "smbs_dose_manual": 3.0}.items():
    ss.setdefault(_k, _v)

# =====================================================
# NAVIGATION
# =====================================================
hdr_ph = st.empty()
if ss.get("nav_main") not in MAIN_TABS:
    ss["nav_main"] = MAIN_TABS[0]


def _cb_nav(key, value):
    ss[key] = value


with st.sidebar:
    md('<div class="sb-brand">💧 HSKH<small>RO Calculator</small></div>')
    side_status = st.empty()
    md('<div class="sb-h">Design steps</div>')
    try:
        _nav_box = st.container(key="sidenav")
    except TypeError:
        _nav_box = st.container()
    with _nav_box:
        for _i, _label in enumerate(MAIN_TABS):
            st.button(_label, key=f"ui_nav_{_i}", on_click=_cb_nav, args=("nav_main", _label),
                      type="primary" if ss["nav_main"] == _label else "secondary")
main = ss["nav_main"].split(" ", 1)[1]

flash = ss.pop("_flash", None)
if flash:
    getattr(st, flash[0])(flash[1])


def flow_view(m3h):
    return (m3h * GPM, "gpm") if ss.get("flow_unit") == "gpm" else (m3h, "m³/h")


def pressure_view(psi):
    return (psi / PSI, "bar") if ss.get("pressure_unit") == "bar" else (psi, "psi")


# =====================================================
# VIEW: PROJECTS
# =====================================================
def view_projects():
    page_title("📁 Projects")
    d = design_calc()
    with card("Design Snapshot", "🎯"):
        if d:
            fv, fu = flow_view(d["q"])
            tiles([("Water type", ss.get("water_type", "")), ("Product flow", f"{fv:.2f} {fu}"), ("Passes", d["passes"]),
                   ("Membrane", f"{d['m1']['vendor']} {d['m1']['model']}"), ("Overall recovery", f"{d['overall_rec']:.1f} %"),
                   ("Flux by pass", " / ".join(f"{e['calc']['flux']:.1f}" for e in d["pl"]) + " gfd"),
                   ("Specific energy", f"{d['spec_kwh_kgal']:.2f} kWh/kgal"), ("Product TDS", f"{d['tds_product']:.1f} mg/L")])
        else:
            st.info("Enter the feed water and the RO design to see the snapshot.")

    with card("Project Information", "📋"):
        c = st.columns(3)
        with c[0]:
            w_text("Project name", "project_name")
            w_text("Client", "pi_client")
        with c[1]:
            w_text("Location", "pi_location")
            w_text("Prepared by", "pi_engineer")
        with c[2]:
            w_text("Project number", "pi_number")
            w_text("Revision", "pi_revision", "0")
        w_area("Comments", "pi_comments", height=70)

    with card("Project File", "💾"):
        c = st.columns([1, 1, 1.2, 1.4])
        with c[0]:
            st.button("🆕 New Project", key="ui_new", on_click=_cb_new)
        with c[1]:
            if st.button("💾 Save now", key="ui_save"):
                ss["_save_clicked"] = True
        with c[2]:
            w_check("Auto-save to folder", "autosave_disk", True)
        with c[3]:
            st.download_button("⬇ Download project", data=project_json(),
                               file_name=f"{_safe_name(ss.get('project_name', 'Project'))}{PROJECT_EXT}", mime="application/json", key="ui_dl_proj")
        st.file_uploader(f"Upload a project file ({PROJECT_EXT})", type=[PROJECT_EXT.strip("."), "json"], key="ui_upload", on_change=_cb_upload)
        st.caption(f"Every project is stored in its own folder under: {PROJECT_DIR}")

    with card("All Projects", "🗂"):
        q = st.text_input("Search projects", key="ui_search", placeholder="Type part of a project, client or membrane name…")
        items = list_projects()
        if q:
            ql = q.lower()
            items = [p for p in items if ql in f"{p['name']} {p['client']} {p['membrane']} {p['water']}".lower()]
        if not items:
            st.info("No saved projects yet. Your current project is saved automatically.")
        else:
            h = st.columns([2.6, 1.6, 2.0, 1.4, 0.9, 1.3, 1])
            for col, text in zip(h, ["Project", "Client", "Membrane · water", "Product flow", "Passes", "Edited", ""]):
                col.markdown(f'<span class="lhead">{text}</span>', unsafe_allow_html=True)
            current = str(ss.get("_last_path", "")).replace("\\", "/")
            for p in items:
                r = st.columns([2.6, 1.6, 2.0, 1.4, 0.9, 1.3, 1])
                r[0].markdown(f"**{hesc(p['name'] or '')}**{' 🟢' if current.endswith(p['rel']) else ''}", unsafe_allow_html=True)
                r[1].markdown(hesc(str(p["client"] or "-")))
                r[2].markdown(hesc(f"{p['membrane'] or '-'} · {p['water'] or '-'}"))
                r[3].markdown(f"{fmt(p['flow'] or 0, 1)} m³/h")
                r[4].markdown(str(p["passes"] or 1))
                r[5].markdown(_ago(p["mtime"]))
                r[6].button("Open", key=f"ui_open_{p['rel']}", on_click=_cb_open_path, args=(p["rel"],))


# =====================================================
# VIEW: FEED WATER
# =====================================================
def ion_block(title, table, fa):
    eq = {r["key"]: r["caco3"] for r in fa["rows"]}
    with card(title):
        h = st.columns([0.7, 1.7, 1.3])
        h[1].markdown('<span class="lhead">mg/L</span>', unsafe_allow_html=True)
        h[2].markdown('<span class="lhead">as CaCO₃</span>', unsafe_allow_html=True)
        for key, label, mw, z, lam in table:
            a, b, c = st.columns([0.7, 1.7, 1.3])
            a.markdown(f"**{label}**")
            with b:
                w_number(f"{label} (mg/L)", key, 0.0, label_visibility="collapsed", min_value=0.0, format="%.4g")
            c.markdown(f'<span class="eq">{eq.get(key, 0.0):.2f}</span>', unsafe_allow_html=True)


def view_feed():
    page_title("💧 Feed Water Analysis")
    with card("Import Water Analysis (IMS Excel)", "📂"):
        c = st.columns([3, 1, 1])
        up = c[0].file_uploader("IMS Excel file", type=["xlsx"], key="ui_ims_upload", label_visibility="collapsed")
        if c[1].button("Load file", key="ui_ims_load"):
            if up is None:
                st.warning("Please select the IMS Excel file")
            else:
                try:
                    df = pd.read_excel(up, header=1, engine="openpyxl").dropna(how="all")
                    water = dict(zip(df["Species"].astype(str).str.strip(), df["Raw water"]))
                    mapping = {"Calcium": "ca", "Magnesium": "mg", "Sodium": "na", "Potassium": "k", "Ammonium": "nh4", "Strontium": "sr",
                               "Barium": "ba", "Fluoride": "f", "Chloride": "cl", "Sulfate": "so4", "Nitrate": "no3", "Carbonate": "co3",
                               "Bicarbonate": "hco3", "Bromide": "br", "Boron": "boron", "Silica": "sio2", "pH": "ph", "Temperature": "temp_c"}
                    for species, key in mapping.items():
                        v = water.get(species, None)
                        if v is None or pd.isna(v):
                            if key in ("ph", "temp_c"):
                                continue
                            v = 0.0
                        ss[key] = SAVED[key] = float(v)
                    st.success("✅ IMS water analysis loaded")
                except Exception as e:
                    st.error(f"Could not read the file: {e}")
        c[2].button("Load IMSDesign example", key="ui_example", on_click=_cb_example)

    with card("Feed Parameters", "⚙️"):
        c = st.columns([1.3, 1.3, 1, 1, 1])
        with c[0]:
            w_select("Water type", WATER_TYPES, "water_type", "Municipal Water")
        with c[1]:
            md(f'<div style="height:.4rem"></div><div class="tile"><div class="t-l">Recommended feed requirement</div><div class="t-v">{hesc(SDI_REQ[ss["water_type"]])}</div></div>')
        with c[2]:
            w_number("SDI15", "sdi", 0.0, min_value=0.0)
        with c[3]:
            w_number("pH", "ph", 7.0, min_value=0.0, max_value=14.0, format="%.2f")
        with c[4]:
            w_number("Temperature (°C)", "temp_c", 25.0, min_value=0.0, max_value=60.0, format="%.1f")
        c = st.columns([1.2, 1, 1])
        with c[0]:
            w_check("Calculate CO₂ from pH and HCO₃", "calc_co2", True)
        with c[1]:
            if not ss.get("calc_co2", True):
                w_number("CO₂ (mg/L)", "co2", 0.0, min_value=0.0)

    fa = feed_analysis()
    cols = st.columns(3)
    with cols[0]:
        ion_block("Cations", CATIONS, fa)
    with cols[1]:
        ion_block("Anions", ANIONS, fa)
    with cols[2]:
        with card("Neutral species"):
            w_number("Silica (SiO₂) mg/L", "sio2", 0.0, min_value=0.0, format="%.4g")
            w_number("Boron (B) mg/L", "boron", 0.0, min_value=0.0, format="%.4g")
            st.markdown("**CO₂ (mg/L)**")
            st.markdown(f"**{fa['c']['co2']:.2f}** {'(calculated)' if ss.get('calc_co2', True) else '(entered)'}")

    fa = feed_analysis()
    with card("Charge Balance & Water Summary", "🧮"):
        cls = "good" if abs(fa["cbe"]) <= 5 else ("warn" if abs(fa["cbe"]) <= 10 else "bad")
        tiles([("Cations", f"{fa['cat']:.3f} meq/L"), ("Anions", f"{fa['an']:.3f} meq/L"),
               ("Charge balance", f"{fa['cbe']:+.2f} %", cls), ("TDS", f"{fa['tds']:.1f} mg/L"),
               ("Hardness", f"{fa['hardness']:.1f} mg/L CaCO₃"), ("Alkalinity", f"{fa['alk']:.1f} mg/L CaCO₃"),
               ("Conductivity @ 25 °C", f"{fa['cond']:.0f} µS/cm"), ("Osmotic pressure", f"{fa['osm_bar']:.2f} bar · {fa['osm_bar'] * PSI:.1f} psi")])
        if abs(fa["cbe"]) > 10:
            st.warning("Charge balance failed - check the analysis. You can balance it with Na⁺ (excess anions) or Cl⁻ (excess cations).")
            diff = fa["cat"] - fa["an"]
            if diff > 0:
                st.button(f"Add Cl⁻ {diff * 35.453:.2f} mg/L", key="ui_bal", on_click=_cb_set, args=("cl", round(_f("cl") + diff * 35.453, 3)))
            else:
                st.button(f"Add Na⁺ {-diff * 22.99:.2f} mg/L", key="ui_bal", on_click=_cb_set, args=("na", round(_f("na") - diff * 22.99, 3)))

    with card("Saturations (raw water)", "🧪"):
        s = fa["sat"]
        tiles([("LSI", f"{fa['lsi']:+.2f}", "good" if fa["lsi"] <= 0 else "warn"), ("Saturation pH (pHs)", f"{fa['phs']:.2f}"),
               ("CaSO₄", f"{s['CaSO4']:.1f} %", "bad" if s["CaSO4"] > 100 else "good"), ("BaSO₄", f"{s['BaSO4']:.1f} %", "bad" if s["BaSO4"] > 100 else "good"),
               ("SrSO₄", f"{s['SrSO4']:.1f} %", "bad" if s["SrSO4"] > 100 else "good"), ("CaF₂", f"{s['CaF2']:.2f} %", "bad" if s["CaF2"] > 100 else "good"),
               ("SiO₂", f"{s['SiO2']:.1f} %", "bad" if s["SiO2"] > 100 else "good")])
        st.caption("Indicative saturations from ideal solubility products (Davies activity). The concentrate saturations are on the RO Design and Chemicals pages.")


# =====================================================
# VIEW: RO DESIGN
# =====================================================
def mem_select(n):
    lib = load_library()
    mems = lib["membranes"]
    vendors = sorted({m["vendor"] for m in mems} | set(lib["vendors"]))
    v = w_select("Vendor", vendors, f"vendor{n}", "DuPont")
    vm = [m for m in mems if m["vendor"] == v]
    s = w_select("Series", sorted({m["series"] for m in vm}), f"series{n}")
    w_select("Membrane model", [m["model"] for m in vm if m["series"] == s], f"model{n}")
    return membrane_lookup(ss.get(f"vendor{n}"), ss.get(f"model{n}"))


def stage_inputs(n, nstages):
    cols = st.columns(3)
    for i in range(1, 4):
        with cols[i - 1]:
            if i <= nstages:
                dv, de = DEF_STAGE[n][i]
                w_number(f"Stage {i} - vessels", f"p{n}_s{i}_v", dv, min_value=1)
                w_number(f"Stage {i} - membranes/vessel", f"p{n}_s{i}_e", de, min_value=1, max_value=8)


def flow_svg(d):
    """Process flow diagram (3D-style symbols, large text, scales to the page width - no scrolling):
    UF -> service water tank -> supply pump -> cartridge filter -> chemical dosing -> RO feed pump -> pass 1..N -> final RO product tank -> users,
    with permeate / concentrate destinations (drain, CIP skid, product tank, recycle). Returns (html, iframe height)."""
    fu = ss.get("flow_unit", "m³/h")
    k = GPM if fu == "gpm" else 1.0
    pu = ss.get("pressure_unit", "psi")
    pk = 1 / PSI if pu == "bar" else 1.0
    pl = d["pl"]
    npass = len(pl)
    cp = chemical_program(d)
    crow = {r["name"]: r for r in cp["rows"]}
    MY, INK = 290, "#0F2233"
    pipes, eq = [], []
    PIPE = {"feed": ("#17497F", "#3F93E0", "#C4E3FF", 9), "perm": ("#09697A", "#4FCBDD", "#DAF8FC", 9),
            "conc": ("#8A3B0C", "#E8883A", "#FFD6AE", 9), "chem": ("#4C2070", "#9A63C9", "#E6D2F7", 5)}

    def cyl(i, dark, light, mid):
        return (f'<linearGradient id="{i}" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="{dark}"/><stop offset=".28" stop-color="{light}"/>'
                f'<stop offset=".6" stop-color="{mid}"/><stop offset="1" stop-color="{dark}"/></linearGradient>')

    def lin(i, c1, c2, c3=None, vertical=True):
        a = 'x1="0" y1="0" x2="0" y2="1"' if vertical else 'x1="0" y1="0" x2="1" y2="1"'
        mid = f'<stop offset=".5" stop-color="{c3}"/>' if c3 else ""
        return f'<linearGradient id="{i}" {a}><stop offset="0" stop-color="{c1}"/>{mid}<stop offset="1" stop-color="{c2}"/></linearGradient>'

    defs = ("<defs>"
            + cyl("cBlue", "#1F5FA6", "#E1F0FD", "#7DB6EA") + cyl("cGreen", "#1B8F5A", "#E3F8EB", "#7FD1A3") + cyl("cPurple", "#5E2A86", "#F3E9FC", "#B995DE")
            + cyl("cGrey", "#59646F", "#F4F6F8", "#AEB8C2") + cyl("cMotor", "#3F4852", "#D3DAE1", "#7A8794")
            + lin("tBlue", "#F4FAFF", "#8FC2EE", vertical=False) + lin("tGreen", "#F2FCF6", "#7FD1A3", vertical=False)
            + lin("tPurple", "#FAF4FF", "#B995DE", vertical=False) + lin("tGrey", "#FFFFFF", "#AEB8C2", vertical=False)
            + lin("vOrange", "#FFE3BE", "#B5651D", "#F4A850") + lin("vBox", "#FFFFFF", "#D5E6F6") + lin("vTag", "#FFFFFF", "#D3DCE4")
            + lin("vUF", "#F2FBFF", "#6DB7D2", "#A9DCEC")
            + '<linearGradient id="vBg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#F6F9FC"/><stop offset=".25" stop-color="#C9D7E5"/><stop offset=".5" stop-color="#EEF3F8"/>'
              '<stop offset=".75" stop-color="#B9CADB"/><stop offset="1" stop-color="#E4ECF4"/></linearGradient>'
            + '<radialGradient id="sph" cx=".35" cy=".3" r=".85"><stop offset="0" stop-color="#FFFFFF"/><stop offset=".5" stop-color="#BBD8F2"/><stop offset="1" stop-color="#4E86BE"/></radialGradient>'
            + '<radialGradient id="sphP" cx=".35" cy=".3" r=".85"><stop offset="0" stop-color="#FFFFFF"/><stop offset=".5" stop-color="#DCC6F2"/><stop offset="1" stop-color="#7B4BA8"/></radialGradient>'
            + '<radialGradient id="sphW" cx=".35" cy=".3" r=".85"><stop offset="0" stop-color="#FFFFFF"/><stop offset="1" stop-color="#C5CFD9"/></radialGradient>'
            + '<filter id="sh" x="-25%" y="-25%" width="150%" height="150%"><feDropShadow dx="2" dy="3" stdDeviation="2.2" flood-color="#0B2540" flood-opacity=".32"/></filter>'
            + "</defs>")

    def txt(x, y, s, size=13, anchor="middle", weight=400, fill=INK):
        return f'<text x="{x:.1f}" y="{y:.1f}" text-anchor="{anchor}" font-size="{size}" font-weight="{weight}" fill="{fill}">{hesc(str(s))}</text>'

    def pipe(x1, y1, x2, y2, kind="feed", w=None, dash=False):
        dark, mid, light, w0 = PIPE[kind]
        w = w or w0
        da = ' stroke-dasharray="9 6"' if dash else ""
        ox, oy = (0, -w * 0.2) if abs(y1 - y2) < 0.01 else (-w * 0.2, 0)
        pipes.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{dark}" stroke-width="{w + 3}"{da}/>'
                     f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{mid}" stroke-width="{w - 0.5}"{da}/>'
                     f'<line x1="{x1 + ox:.1f}" y1="{y1 + oy:.1f}" x2="{x2 + ox:.1f}" y2="{y2 + oy:.1f}" stroke="{light}" stroke-width="{max(1.4, w * 0.28):.1f}" stroke-opacity=".9"{da}/>')

    def arrowhead(x, y, dirn, kind):
        dark, mid = PIPE[kind][0], PIPE[kind][1]
        pts = {"r": f"{x},{y} {x - 14},{y - 9} {x - 14},{y + 9}", "d": f"{x},{y} {x - 9},{y - 14} {x + 9},{y - 14}", "u": f"{x},{y} {x - 9},{y + 14} {x + 9},{y + 14}"}[dirn]
        eq.append(f'<polygon points="{pts}" fill="{mid}" stroke="{dark}" stroke-width="1.5"/>')

    def tank(x, y, w, h, cy_id, top_id, stroke):
        ry = 10
        eq.append(f'<g filter="url(#sh)"><ellipse cx="{x + w / 2}" cy="{y + h - ry}" rx="{w / 2}" ry="{ry}" fill="url(#{cy_id})" stroke="{stroke}" stroke-width="1.8"/>'
                  f'<rect x="{x}" y="{y + ry}" width="{w}" height="{h - 2 * ry}" fill="url(#{cy_id})"/>'
                  f'<line x1="{x}" y1="{y + ry}" x2="{x}" y2="{y + h - ry}" stroke="{stroke}" stroke-width="1.8"/>'
                  f'<line x1="{x + w}" y1="{y + ry}" x2="{x + w}" y2="{y + h - ry}" stroke="{stroke}" stroke-width="1.8"/>'
                  f'<ellipse cx="{x + w / 2}" cy="{y + ry}" rx="{w / 2}" ry="{ry}" fill="url(#{top_id})" stroke="{stroke}" stroke-width="1.8"/></g>')

    def pump(cx, cy, r=14, motor=True, sph="sph"):
        eq.append('<g filter="url(#sh)">')
        if motor:
            eq.append(f'<rect x="{cx - r * 0.7:.1f}" y="{cy - r - 15}" width="{r * 1.4:.1f}" height="17" rx="3" fill="url(#cMotor)" stroke="{INK}" stroke-width="1.4"/>'
                      f'<line x1="{cx - r * 0.35:.1f}" y1="{cy - r - 12}" x2="{cx - r * 0.35:.1f}" y2="{cy - r - 1}" stroke="#EEF2F5" stroke-width="1.2"/>')
        eq.append(f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="url(#{sph})" stroke="{INK}" stroke-width="1.8"/>'
                  f'<polygon points="{cx - r * 0.38:.1f},{cy - r * 0.5:.1f} {cx - r * 0.38:.1f},{cy + r * 0.5:.1f} {cx + r * 0.55:.1f},{cy}" fill="{INK}"/></g>')

    def gauge(cx, label):
        eq.append(f'<line x1="{cx}" y1="{MY - 4}" x2="{cx}" y2="{MY - 22}" stroke="{INK}" stroke-width="2.2"/>'
                  f'<circle cx="{cx}" cy="{MY - 31}" r="9.5" fill="url(#sphW)" stroke="{INK}" stroke-width="1.8" filter="url(#sh)"/>'
                  f'<line x1="{cx}" y1="{MY - 31}" x2="{cx + 5}" y2="{MY - 36}" stroke="#C62828" stroke-width="1.8"/>')
        if label:
            eq.append(txt(cx, MY - 48, label, 13, weight=700))

    def chem_tank(x, name, row, alt="", formula="", below=False):
        dose = row["dose"] if row else 0.0
        active = dose > 0
        if below:                                   # tank under the line, dosing pump between tank and line, arrow pointing up
            ty, py = MY + 126, MY + 98
            pipe(x, MY + 6, x, ty + 4, "chem")
            arrowhead(x, MY + 3, "u", "chem")
        else:                                       # tank above the line, arrow pointing down
            ty, py = 12, 120
            pipe(x, 96, x, MY - 6, "chem")
            arrowhead(x, MY - 3, "d", "chem")
        eq.append(f'<g opacity="{1 if active else 0.55}">')
        tank(x - 44, ty, 88, 84, "cPurple", "tPurple", "#5E2A86")
        y1 = ty + (26 if formula else 32)
        eq.append(txt(x, y1, name, 13, weight=800, fill="#2E1247"))
        if formula:
            eq.append(txt(x, y1 + 14, formula, 12, weight=700, fill="#2E1247"))
        eq.append(txt(x, y1 + 17 + (13 if formula else 0), f"{dose:.2f} mg/L" if active else "not dosed", 12, weight=600, fill="#1F1030"))
        eq.append(txt(x, y1 + 33 + (13 if formula else 0), f"{row['l_h']:.2f} L/h" if (active and row) else alt, 12, weight=600, fill="#1F1030"))
        eq.append(f'<circle cx="{x}" cy="{py}" r="12" fill="url(#sphP)" stroke="#4C2070" stroke-width="1.8" filter="url(#sh)"/>'
                  f'<polygon points="{x - 4.5},{py - 7} {x - 4.5},{py + 7} {x + 7.5},{py}" fill="#2E1247"/></g>')

    # ---------------- geometry ----------------
    BW, GAP, BX1 = 176, 138, 856
    PITCH = BW + GAP
    bxs = [BX1 + PITCH * i for i in range(npass)]
    post = [r for r in cp["rows"] if "post-treatment" in r["name"] and r["dose"] > 0]
    E = bxs[-1] + BW
    xt = E + (96 * len(post) + 125 if post else 150)
    TAGW = 235
    tagx = E + 100
    chem1 = d["adj1"]["chem"]
    row_ph = crow.get(f"{chem1} (pass 1 pH)") if chem1 not in ("None", None, "") else None
    hmax = max(42 + len(e["calc"]["rows"]) * 48 + 40 for e in pl)

    # ---------------- upstream ----------------
    pipe(72, MY, 88, MY, "feed")
    pipe(200, MY, 220, MY, "feed")
    pipe(248, MY, 284, MY, "feed")
    pipe(324, MY, 738, MY, "feed")
    pipe(774, MY, bxs[0], MY, "feed")
    arrowhead(bxs[0], MY, "r", "feed")
    ux, uw, uy, uh, ud = 8, 56, MY - 36, 72, 10
    eq.append(f'<g filter="url(#sh)"><polygon points="{ux},{uy} {ux + ud},{uy - ud} {ux + uw + ud},{uy - ud} {ux + uw},{uy}" fill="#D3EEF8" stroke="#0E7FA8" stroke-width="1.6"/>'
              f'<polygon points="{ux + uw},{uy} {ux + uw + ud},{uy - ud} {ux + uw + ud},{uy + uh - ud} {ux + uw},{uy + uh}" fill="#4F9DB8" stroke="#0E7FA8" stroke-width="1.6"/>'
              f'<rect x="{ux}" y="{uy}" width="{uw}" height="{uh}" fill="url(#vUF)" stroke="#0E7FA8" stroke-width="1.8"/></g>')
    eq.append(txt(ux + uw / 2, MY - 1, "UF", 19, weight=800) + txt(ux + uw / 2, MY + 17, "system", 12.5, weight=600))
    tank(88, MY - 76, 112, 152, "cBlue", "tBlue", "#1F5FA6")
    eq.append(txt(144, MY - 26, "SERVICE", 13, weight=800, fill="#0A2A4A") + txt(144, MY - 10, "WATER TANK", 13, weight=800, fill="#0A2A4A")
              + txt(144, MY + 9, "(UF filtrate)", 12, fill="#0A2A4A") + txt(144, MY + 27, f"{d['raw'] * k:.1f} {fu}", 13, weight=800, fill="#0A2A4A"))
    pump(234, MY)
    eq.append(txt(234, MY + 38, "Supply pump", 13, weight=700))
    gauge(266, "")
    eq.append('<g filter="url(#sh)">'
              f'<ellipse cx="304" cy="{MY + 38}" rx="20" ry="8" fill="url(#cGrey)" stroke="{INK}" stroke-width="1.6"/>'
              f'<rect x="284" y="{MY - 38}" width="40" height="76" fill="url(#cGrey)"/><line x1="284" y1="{MY - 38}" x2="284" y2="{MY + 38}" stroke="{INK}" stroke-width="1.6"/>'
              f'<line x1="324" y1="{MY - 38}" x2="324" y2="{MY + 38}" stroke="{INK}" stroke-width="1.6"/>'
              f'<ellipse cx="304" cy="{MY - 38}" rx="20" ry="8" fill="url(#tGrey)" stroke="{INK}" stroke-width="1.6"/></g>')
    eq.append(txt(304, MY + 64, "Cartridge filter", 13, weight=700) + txt(304, MY + 80, "5 µm", 12))
    gauge(346, "")
    chem_tank(425, "NaOCl", crow.get("NaOCl"))                                                                  # above
    chem_tank(490, "SMBS", crow.get("SMBS (Na2S2O5)"), formula="Na₂S₂O₅", below=True)                          # below
    chem_tank(570, chem1 if chem1 not in ("None", None, "") else "NaOH/acid", row_ph)                          # above
    chem_tank(635, "Antiscalant", crow.get("Antiscalant"), below=True)                                         # below
    pump(756, MY, r=18)
    eq.append(txt(756, MY + 42, "RO feed pump", 13, weight=700))

    # ---------------- passes ----------------
    drops = []
    for i, e in enumerate(pl):
        n, c, mem = e["n"], e["calc"], e["mem"]
        bx = bxs[i]
        ns = len(c["rows"])
        hn = 42 + ns * 48 + 40
        y0 = MY - hn / 2
        eq.append(f'<rect x="{bx}" y="{y0}" width="{BW}" height="{hn}" rx="10" fill="url(#vBox)" stroke="#2D7FD3" stroke-width="2.6" filter="url(#sh)"/>')
        eq.append(txt(bx + BW / 2, y0 + 19, f"PASS {n}", 16, weight=800) + txt(bx + BW / 2, y0 + 35, mem["model"], 12.5, fill="#1F3F5C", weight=600))
        last_c = y0 + 42 + (ns - 1) * 48 + 20
        eq.append(f'<line x1="{bx + 5}" y1="{y0 + 62}" x2="{bx + 5}" y2="{last_c}" stroke="#2D7FD3" stroke-width="4"/>'
                  f'<line x1="{bx + BW - 5}" y1="{y0 + 62}" x2="{bx + BW - 5}" y2="{last_c}" stroke="#0B7F91" stroke-width="4"/>')
        for j, r in enumerate(c["rows"]):
            sy = y0 + 42 + j * 48
            eq.append(f'<line x1="{bx + 5}" y1="{sy + 20}" x2="{bx + 11}" y2="{sy + 20}" stroke="#2D7FD3" stroke-width="4"/>'
                      f'<line x1="{bx + BW - 11}" y1="{sy + 20}" x2="{bx + BW - 5}" y2="{sy + 20}" stroke="#0B7F91" stroke-width="4"/>'
                      f'<rect x="{bx + 11}" y="{sy}" width="{BW - 22}" height="40" rx="20" fill="url(#vOrange)" stroke="#8A4A12" stroke-width="1.8" filter="url(#sh)"/>'
                      f'<rect x="{bx + 30}" y="{sy + 3}" width="{BW - 60}" height="8" rx="4" fill="#FFFFFF" opacity=".4"/>')
            eq.append(txt(bx + BW / 2, sy + 18, f"Stage {r['stage']}", 13.5, weight=800, fill="#3A1C04") + txt(bx + BW / 2, sy + 33, f"{r['vessels']} vessels x {r['elements']} el", 12, weight=600, fill="#3A1C04"))
        eq.append(txt(bx + BW / 2, y0 + hn - 22, f"flux {c['flux']:.1f} gfd - rec {c['y'] * 100:.0f} %", 13, weight=800, fill="#154E78")
                  + txt(bx + BW / 2, y0 + hn - 6, f"{c['n_el']} el - {c['area']:,.0f} ft²", 12, weight=600, fill="#1F3F5C"))
        pipe(bx + BW, MY, (bxs[i + 1] - 66 - 14) if i + 1 < npass else xt, MY, "perm")
        gauge(bx - 28, f"{c['pf'] * pk:.0f} {pu}")
        eq.append(txt(bx - 28, MY + 20, f"feed {c['f_m3h'] * k:.1f}", 12, weight=600, fill="#1F3F5C"))
        if i + 1 < npass:
            nxt = bxs[i + 1]
            px = nxt - 66
            pipe(px + 14, MY, nxt, MY, "perm")
            arrowhead(nxt, MY, "r", "perm")
            pump(px, MY)
            eq.append(txt(px, MY + 42, f"Pass {n + 1} feed pump", 13, weight=700))
            eq.append(txt(bx + BW + 8, MY + 24, f"{c['p_m3h'] * k:.1f} {fu}", 13, anchor="start", weight=800, fill="#07505E"))
            nadj = pl[i + 1]["adj"]
            if nadj["chem"] not in ("None", None, ""):
                chem_tank(px - 44, nadj["chem"], crow.get(f"{nadj['chem']} (pass {n + 1} pH)"))
        drops.append((n, bx, MY + hn / 2, c))

    # ---------------- post-treatment, product line, final RO tank ----------------
    for kx, r in enumerate(post):
        chem_tank(E + 60 + 96 * kx, r["name"].split(" ")[0], r)
    arrowhead(xt, MY, "r", "perm")
    fx, ax = xt - 44, xt - 100
    eq.append(f'<rect x="{fx - 17}" y="{MY - 11}" width="34" height="22" rx="3" fill="url(#vTag)" stroke="{INK}" stroke-width="1.6" filter="url(#sh)"/>' + txt(fx, MY + 5, "FT", 12.5, weight=800)
              + txt(fx, MY - 18, f"{d['q'] * k:.1f} {fu}", 13, weight=800, fill="#07505E"))
    eq.append(f'<rect x="{ax - 19}" y="{MY - 11}" width="38" height="22" rx="3" fill="url(#vTag)" stroke="{INK}" stroke-width="1.6" filter="url(#sh)"/>' + txt(ax, MY + 5, "AIT", 12.5, weight=800)
              + txt(ax, MY + 30, f"{comp_cond(d['product']):.1f} µS/cm", 12, weight=600, fill="#1F3F5C"))
    tank(xt, MY - 76, 124, 152, "cGreen", "tGreen", "#1B8F5A")
    eq.append(txt(xt + 62, MY - 30, "FINAL RO", 13, weight=800, fill="#0C3320") + txt(xt + 62, MY - 14, "PRODUCT TANK", 13, weight=800, fill="#0C3320")
              + txt(xt + 62, MY + 8, f"{d['q'] * k:.1f} {fu}", 13, weight=800, fill="#0C3320") + txt(xt + 62, MY + 25, f"TDS {d['tds_product']:.1f} mg/L", 12, weight=600, fill="#0C3320"))
    pipe(xt + 124, MY, xt + 192, MY, "perm")
    arrowhead(xt + 192, MY, "r", "perm")
    eq.append(txt(xt + 158, MY - 16, "To users", 14, weight=800, fill="#0C3320"))

    # ---------------- permeate / concentrate destinations ----------------
    ybase = MY + hmax / 2 + 34
    cur = ybase
    tags = []
    for n, bx, ybot, c in reversed(drops):
        rows = []
        if n == npass:
            rows.append((f"PASS {n} PERMEATE  {c['p_m3h'] * k:.1f} {fu}", "perm", "RO PRODUCT WATER STORAGE TANK", False))
        rows.append((f"PASS {n} PERMEATE - OFF-SPEC", "perm", "DRAIN", False))
        rows.append((f"PASS {n} PERMEATE - CIP", "perm", "CLEAN-IN-PLACE SKID", False))
        rows.append((f"PASS {n} CONCENTRATE - CIP", "conc", "CLEAN-IN-PLACE SKID", False))
        if d["recycle"] and n >= 2:
            rows.append((f"PASS {n} CONC. RECYCLE  {c['c_m3h'] * k:.1f} {fu}", "conc", "RECYCLE TO PASS 1 FEED", True))
        else:
            rows.append((f"PASS {n} CONCENTRATE  {c['c_m3h'] * k:.1f} {fu}", "conc", "DRAIN", False))
        for ri, (label, kind, tag, dash) in enumerate(rows):
            vx = bx + 16 + 13 * (len(rows) - 1 - ri)
            pipe(vx, ybot, vx, cur, kind, w=4, dash=dash)
            pipe(vx, cur, tagx, cur, kind, w=4, dash=dash)
            eq.append(txt(vx + 8, cur - 7, label, 12.5, anchor="start", weight=700))
            tags.append((cur, tag))
            cur += 29
        cur += 10
    for y, tag in tags:
        eq.append(f'<polygon points="{tagx},{y - 12} {tagx + TAGW - 13},{y - 12} {tagx + TAGW},{y} {tagx + TAGW - 13},{y + 12} {tagx},{y + 12}" fill="url(#vTag)" stroke="{INK}" stroke-width="1.5" filter="url(#sh)"/>'
                  + txt(tagx + (TAGW - 8) / 2, y + 4.5, tag, 11.5, weight=800))
    ly = MY + 125
    for j, (kind, label) in enumerate((("feed", "Service water / RO feed"), ("perm", "Permeate"), ("conc", "Concentrate / reject"), ("chem", "Chemical dosing"))):
        yy = ly + 24 * j
        eq.append(f'<line x1="14" y1="{yy}" x2="50" y2="{yy}" stroke="{PIPE[kind][0]}" stroke-width="9"/><line x1="14" y1="{yy}" x2="50" y2="{yy}" stroke="{PIPE[kind][1]}" stroke-width="6.5"/>'
                  f'<line x1="14" y1="{yy - 1.8}" x2="50" y2="{yy - 1.8}" stroke="{PIPE[kind][2]}" stroke-width="1.8"/>' + txt(60, yy + 4.5, label, 13, anchor="start", weight=600))

    W = max(tagx + TAGW, xt + 200) + 24
    H = max(cur + 14, ly + 110, MY + 230)
    svg = (f'<svg viewBox="0 0 {W} {H}" width="100%" xmlns="http://www.w3.org/2000/svg" style="display:block;height:auto;margin:0 auto;" preserveAspectRatio="xMidYMin meet">{defs}'
           f'<rect x="1" y="1" width="{W - 2}" height="{H - 2}" rx="12" fill="url(#vBg)" stroke="#2A2F36" stroke-width="2"/>' + "".join(pipes) + "".join(eq) + "</svg>")
    html = ("<html><head><meta charset=\"utf-8\"></head><body style=\"margin:0;overflow:hidden;background:transparent;font-family:'Segoe UI',Arial,sans-serif;\">"
            f'<div id="wrap">{svg}</div>'
            "<script>function fit(){try{var h=document.getElementById('wrap').getBoundingClientRect().height;"
            "window.frameElement.style.height=(h+4)+'px';}catch(e){}}"
            "window.addEventListener('load',fit);window.addEventListener('resize',fit);setTimeout(fit,250);setTimeout(fit,900);</script></body></html>")
    return html, int(H * min(1.0, 850 / W)) + 12


def view_design():
    page_title("📈 RO Design")
    lib = load_library()
    with card("System", "⚙️"):
        c = st.columns([1.2, 1, 1.3, 1, 1])
        with c[0]:
            w_unit_number(f"Plant product flow ({ss.get('flow_unit', 'm³/h')})", "product_flow", 37.5, "flow_unit", FLOW_UNITS, min_value=0.1, format="%.2f")
        with c[1]:
            w_select("Flow unit", ["m³/h", "gpm"], "flow_unit", "m³/h")
        with c[2]:
            npass = int(w_radio("RO passes", list(range(1, MAX_PASSES + 1)), "passes", 1, horizontal=True))
        with c[3]:
            w_number("Target product TDS (mg/L)", "target_tds", 10.0, min_value=0.0)
        with c[4]:
            w_select("Pressure unit", ["psi", "bar"], "pressure_unit", "psi")
        c = st.columns([1, 1.4, 1])
        with c[0]:
            w_number("Permeate back-pressure (psi)", "perm_pressure", 0.0, min_value=0.0)
        with c[1]:
            if npass >= 2:
                w_check("Recycle the pass-2 and later concentrates to the pass-1 feed", "recycle", True)
        with c[2]:
            st.button("Load IMSDesign example", key="ui_example2", on_click=_cb_example)

    flow_slot = st.container()      # flow diagram is drawn here, once the design is calculated

    with card("Membrane Selection", "🧫"):
        mems = []
        for row_start in range(1, npass + 1, 2):
            cols = st.columns(2)
            for k_, n in enumerate(range(row_start, min(row_start + 2, npass + 1))):
                with cols[k_]:
                    sub(f"Pass {n}")
                    if n == 1:
                        m = mem_select(1)
                    else:
                        same = w_check("Same membrane as pass 1", f"same{n}", True)
                        if same:
                            m = mems[0]
                            st.caption("Using the pass 1 membrane.")
                        else:
                            m = mem_select(n)
                    mems.append(m)
        shown = [(n, m) for n, m in enumerate(mems, start=1) if m]
        if shown:
            first = shown[0][1]
            tiles([(f"Pass {n}", f"{m['vendor']} {m['model']} · {m['type']}") for n, m in shown] +
                  [("Element size", f"{first['size_in']:.0f} in"), ("Active area / element", f"{first['area_ft2']:.0f} ft²"), ("Nominal rejection", f"{first['rejection']:.2f} %"),
                   ("Permeability A (25 °C)", f"{first['a_w']:.3f} gfd/psi"), ("Reference tool", vendor_profile(first["vendor"]).get("tool", "") or "-")])
            if any(str(m.get("source", "")).upper().startswith("TEMPLATE") for _, m in shown):
                st.caption("⚠ Template membrane data - replace on the Library page.")
            notes = [f"{m['model']}: {m['notes']}" for _, m in shown if m.get("notes")]
            if notes:
                st.caption("ℹ " + " | ".join(dict.fromkeys(notes)))

    with card("Train Information", "🚂"):
        widths = [1.5] + [1] * npass
        h = st.columns(widths)
        for n in range(1, npass + 1):
            h[n].markdown(f'<span class="lhead">Pass {n}</span>', unsafe_allow_html=True)
        specs = [("Permeate recovery (%)", "rec", dict(min_value=1.0, max_value=99.0)),
                 ("Membrane age (years)", "age", dict(min_value=0.0)),
                 ("Flux decline (% / year)", "decl", dict(min_value=0.0, max_value=50.0)),
                 ("Salt passage increase (% / year)", "sp", dict(min_value=0.0))]
        for label, base, kw in specs:
            r = st.columns(widths)
            r[0].markdown(f"**{label}**")
            for n in range(1, npass + 1):
                with r[n]:
                    w_number(label, f"p{n}_rec" if base == "rec" else f"{base}{n}", pass_default(n, base), label_visibility="collapsed", **kw)
        r = st.columns(widths)
        r[0].markdown("**Fouling factor = (1 − decline)^age**")
        for n in range(1, npass + 1):
            r[n].markdown(f"**{(1 - _f(f'decl{n}', pass_default(n, 'decl')) / 100) ** _f(f'age{n}', pass_default(n, 'age')):.3f}**")

    with card("System Specifications", "🏗"):
        for n in range(1, npass + 1):
            sub(f"Pass {n}")
            n_st = int(w_select(f"Pass {n} stages", [1, 2, 3], f"p{n}_stages", 3 if n == 1 else 2))
            stage_inputs(n, n_st)

    d = design_calc()
    if not d:
        with flow_slot:
            with card("Flow diagram", "🗺"):
                st.info("Select the membranes and enter the product flow to see the flow diagram.")
        with card("Caution messages — red invalidates the design", "⚠️"):
            st.warning("Select the membranes and enter the product flow to calculate the design.")
        return
    with flow_slot:
        with card("Flow diagram", "🗺"):
            _html, _h = flow_svg(d)
            components.html(_html, height=_h, scrolling=False)
    with card("Flows & Flux", "📊"):
        for e in d["pl"]:
            pdx = e["calc"]
            sub(f"Pass {e['n']}")
            tiles([("Feed", "{:.2f} m³/h · {:.1f} gpm".format(pdx["f_m3h"], pdx["f"])), ("Permeate", "{:.2f} m³/h · {:.1f} gpm".format(pdx["p_m3h"], pdx["p"])),
                   ("Concentrate", "{:.2f} m³/h · {:.1f} gpm".format(pdx["c_m3h"], pdx["c"])), ("Average flux", f"{pdx['flux']:.2f} gfd"),
                   ("Elements / vessels", f"{pdx['n_el']} / {pdx['n_vessels']}"), ("Membrane area", f"{pdx['area']:,.0f} ft²"),
                   ("Recovery", f"{pdx['y'] * 100:.1f} %")])
        tiles([("Raw feed flow", "{:.2f} m³/h · {:.1f} gpm".format(d["raw"], d["raw"] * GPM)), ("Plant product", "{:.2f} m³/h · {:.1f} gpm".format(d["q"], d["q"] * GPM)),
               ("Overall recovery", f"{d['overall_rec']:.1f} %")])
    with card("Stage Details", "🧱"):
        for e in d["pl"]:
            pdx = e["calc"]
            sub(f"Pass {e['n']}")
            show_df(pd.DataFrame([{"Stage": r["stage"], "Vessels × elements": f"{r['vessels']} × {r['elements']}", "Area (ft²)": round(r["area"]),
                                   "Feed (gpm)": round(r["feed"], 1), "Permeate (gpm)": round(r["perm"], 1), "Conc (gpm)": round(r["conc"], 1),
                                   "Feed / vessel": round(r["feed_v"], 1), "Conc / vessel": round(r["conc_v"], 1),
                                   "Lead element recovery %": round(r["lead_rec"], 1), "ΔP stage (psi)": round(r["dp_stage"], 1)} for r in pdx["rows"]]), hide_index=True)

    checks = run_checks(d)
    with card("Caution messages — red invalidates the design", "⚠️"):          # below the input tables
        status_banner(checks, "RO design")
        checklist(checks)
        water = ss.get("water_type", "Municipal Water")
        st.caption("Recommended maximum flux: " + " · ".join(f"pass {e['n']} {guideline_flux(water, e['n'], e['mem']['vendor']):.1f} gfd" for e in d["pl"]) +
                   f" (pass 1 for {water}; later passes are fed with RO permeate). Editable on the Library page.")


# =====================================================
# VIEW: CHEMICALS
# =====================================================
def view_chem():
    page_title("🧪 Chemical Requirements")
    d = design_calc()
    if not d:
        st.warning("Complete the RO Design page first.")
        return
    lib = load_library()
    fa = d["fa"]
    q_view, q_unit = flow_view(d["q"])

    with card("Pass 1 feed pH adjustment (acid / NaOH)", "⚗️"):
        c = st.columns([1, 1, 1, 1, 1])
        with c[0]:
            chem = w_select("Chemical", ["None", "H2SO4", "HCl", "NaOH"], "p1_chem", "None")
        with c[1]:
            w_number("Target feed pH", "p1_ph", float(fa["ph"]), min_value=2.0, max_value=12.0, format="%.2f", disabled=chem == "None")
        defc = CHEM_DEFAULTS.get(chem, (100.0, 1.0))
        with c[2]:
            w_number("Solution strength (%)", "p1_conc", defc[0], min_value=1.0, max_value=100.0, disabled=chem == "None")
        with c[3]:
            w_number("Specific gravity", "p1_sg", defc[1], min_value=0.5, max_value=2.5, format="%.2f", disabled=chem == "None")
        with c[4]:
            w_number("Unit cost (per kg of solution)", "cost_p1", 0.0, min_value=0.0, disabled=chem == "None")
        d = design_calc()
        if d["adj1"]["chem"] != "None":
            tiles([("Dose (100 %)", f"{d['adj1']['dose']:.2f} mg/L"), ("Feed pH", f"{fa['ph']:.2f} → {d['ph1']:.2f}"),
                   ("Raw alkalinity", f"{fa['alk']:.1f} mg/L CaCO₃")])
            if d["adj1"]["note"]:
                st.warning(d["adj1"]["note"])
        st.caption("Dose = alkalinity change needed to reach the target pH, with total carbonate (HCO₃ + CO₃ + CO₂) conserved.")

    with card("Pretreatment: SMBS, antiscalant, NaOCl", "🧴"):
        sub("SMBS - sodium metabisulfite Na₂S₂O₅ (dechlorination)")
        c = st.columns([1.5, 1, 1, 1])
        with c[0]:
            w_radio("SMBS dose basis", ["Manual dose", "From free chlorine"], "smbs_mode", "Manual dose", horizontal=True)
        with c[1]:
            w_number("Manual dose (mg/L)", "smbs_dose_manual", 3.0, min_value=0.0, step=0.5, disabled=ss.get("smbs_mode") != "Manual dose")
        with c[2]:
            w_number("Free chlorine (mg/L)", "free_cl", 0.0, min_value=0.0, step=0.1)
        with c[3]:
            w_number("SMBS : Cl₂ ratio", "smbs_ratio", 3.0, min_value=1.0, step=0.1, disabled=ss.get("smbs_mode") == "Manual dose")
        c = st.columns(4)
        with c[0]:
            w_number("Strength (%)", "smbs_conc", 10.0, min_value=1.0, max_value=100.0)
        with c[1]:
            w_number("Specific gravity", "smbs_sg", 1.10, min_value=0.5, max_value=2.5, format="%.2f")
        with c[2]:
            w_number("Unit cost / kg solution", "cost_smbs", 0.0, min_value=0.0)
        with c[3]:
            tiles([("SMBS dose applied", f"{smbs_dose():.2f} mg/L")])
        st.caption("Na₂S₂O₅ removes free chlorine / oxidants before the polyamide membrane. Calculated basis: 3 mg SMBS per mg free chlorine (theoretical 1.34); manual basis: set the dose directly.")
        sub("Antiscalant")
        names = [a["product"] for a in lib["antiscalants"]]
        c = st.columns([1.4, 1.1, 1, 1, 1, 1])
        with c[0]:
            w_select("Product", names, "as_product", "Vitec 3000")
        with c[1]:
            w_radio("Dose", ["Recommended", "Manual dose"], "as_mode", "Recommended", horizontal=True)
        with c[2]:
            w_number("Manual dose (mg/L)", "as_dose_manual", 3.0, min_value=0.0, disabled=ss.get("as_mode") != "Manual dose")
        with c[3]:
            w_number("Strength (%)", "as_conc", 40.0, min_value=1.0, max_value=100.0)
        with c[4]:
            w_number("Specific gravity", "as_sg", 1.0, min_value=0.5, max_value=2.5, format="%.2f")
        with c[5]:
            w_number("Unit cost / kg solution", "cost_as", 0.0, min_value=0.0)
        sub("NaOCl (disinfection)")
        c = st.columns(4)
        with c[0]:
            w_number("Dose (mg/L as 100 %)", "naocl_dose", 0.0, min_value=0.0)
        with c[1]:
            w_number("Strength (%) ", "naocl_conc", 10.0, min_value=1.0, max_value=100.0)
        with c[2]:
            w_number("Specific gravity ", "naocl_sg", 1.30, min_value=0.5, max_value=2.5, format="%.2f")
        with c[3]:
            w_number("Unit cost / kg solution ", "cost_naocl", 0.0, min_value=0.0)

    d = design_calc()
    for n in range(2, d["passes"] + 1):
        last = n == d["passes"]
        with card(f"Pass {n}: pH adjustment" + (" and boron" if last else ""), "⚗️"):
            c = st.columns(5)
            with c[0]:
                chem_n = w_select(f"Chemical (pass {n})", ["NaOH", "None", "H2SO4", "HCl"] if n == 2 else ["None", "NaOH", "H2SO4", "HCl"],
                                  f"p{n}_chem", "NaOH" if n == 2 else "None")
            with c[1]:
                w_number(f"Pass {n} feed pH", f"p{n}_ph", 8.2, min_value=6.0, max_value=11.0, step=0.1, format="%.2f", disabled=chem_n == "None")
            dc = CHEM_DEFAULTS.get(chem_n, (100.0, 1.0))
            with c[2]:
                w_number(f"Strength (%) - pass {n}", f"p{n}_conc", dc[0], min_value=1.0, max_value=100.0, disabled=chem_n == "None")
            with c[3]:
                w_number(f"Specific gravity - pass {n}", f"p{n}_sg", dc[1], min_value=0.5, max_value=2.5, format="%.2f", disabled=chem_n == "None")
            with c[4]:
                w_number(f"Unit cost / kg solution - pass {n}", f"cost_p{n}", 0.0, min_value=0.0, disabled=chem_n == "None")
            d = design_calc()
            e, prev = d["pl"][n - 1], d["pl"][n - 2]
            items = [("Dose (100 %)", f"{e['adj']['dose']:.2f} mg/L"),
                     (f"Pass {n - 1} permeate pH → pass {n} feed pH", f"{prev['ph_perm']:.2f} → {e['ph_feed']:.2f}"),
                     (f"Pass {n - 1} permeate CO₂", f"{prev['perm']['co2']:.1f} mg/L"),
                     ("Boron rejection (pH)", f"{boron_rejection(e['ph_feed']):.1f} %")]
            if last:
                items.append(("Feed boron → product boron", f"{fa['c']['boron']:.3f} → {d['product']['boron']:.3f} mg/L"))
            tiles(items)
            if e["adj"]["note"]:
                st.warning(e["adj"]["note"])
            st.caption("Raising the pH converts permeate CO₂ to HCO₃⁻/CO₃²⁻ (rejected in the next pass) and improves boron rejection.")

    with card("Post-treatment (permeate conditioning)", "🧂"):
        c = st.columns(4)
        for i, (key, label, mw) in enumerate(POST_CHEMS):
            with c[i % 4]:
                w_number(f"{label} (mg/L, 100 %)", key, 0.0, min_value=0.0)
        d = design_calc()
        pt = post_treatment(d)
        tiles([("Product pH", f"{d['product_ph']:.2f} → {pt['ph']:.2f}"), ("TDS", f"{d['tds_product']:.2f} → {pt['tds']:.2f} mg/L"),
               ("Alkalinity", f"{pt['alk']:.1f} mg/L CaCO₃"), ("Hardness", f"{pt['hardness']:.1f} mg/L CaCO₃"),
               ("LSI", f"{pt['lsi']:+.2f}", "good" if -0.5 <= pt["lsi"] <= 0.5 else "warn")])
        st.caption("Final pH from the carbonate system: alkalinity added by the chemicals, total carbonate conserved.")

    d = design_calc()
    cp = chemical_program(d)
    with card("Concentrate scaling indicators", "📉"):
        s = d["sat_conc"]
        tiles([("Concentration factor", f"{d['cf']:.2f}"), ("Concentrate pH", f"{d['ph_conc']:.2f}"),
               ("LSI (concentrate)", f"{d['lsi_conc']:+.2f}", "good" if d["lsi_conc"] <= 0 else "warn"),
               ("CaSO₄", f"{s['CaSO4']:.0f} %", "bad" if s["CaSO4"] > 100 else "good"), ("BaSO₄", f"{s['BaSO4']:.0f} %", "bad" if s["BaSO4"] > 100 else "good"),
               ("SrSO₄", f"{s['SrSO4']:.0f} %", "bad" if s["SrSO4"] > 100 else "good"), ("SiO₂", f"{s['SiO2']:.0f} %", "bad" if s["SiO2"] > 100 else "good"),
               ("Antiscalant recommended", f"{cp['antiscalant_rec']:.2f} mg/L")])
    with card("All chemicals - dose, consumption and cost", "📋"):
        rows = [r for r in cp["rows"] if r["dose"] > 0]
        if rows:
            show_df(pd.DataFrame([{"Chemical": r["name"], "Dosing point": r["point"], "Dose (mg/L, 100 %)": round(r["dose"], 2), "Flow (m³/h)": round(r["flow"], 2),
                                   "kg/h (100 %)": round(r["kg_h"], 3), "Solution": f"{r['conc']:.0f} % · SG {r['sg']:.2f}",
                                   "Solution (kg/h)": round(r["sol_kg_h"], 3), "Solution (L/h)": round(r["l_h"], 2), "kg/day (100 %)": round(r["kg_day"], 1),
                                   "Solution (L/day)": round(r["l_day"], 1), "Cost / day": round(r["cost_day"], 1)} for r in rows]), hide_index=True)
            tiles([("Total chemical cost / day", f"{cp['cost_day']:,.1f}"), ("Chemical cost per m³ product", f"{cp['cost_m3']:.4f}"),
                   ("Day-tank volume (1 day)", ", ".join(f"{r['name'].split(' ')[0]} {r['l_day']:.0f} L" for r in rows if r['l_day'] > 0) or "-")])
        else:
            st.info("No chemical is dosed. Enter doses above.")


# =====================================================
# VIEW: HYDRAULICS & POWER
# =====================================================
def view_hyd():
    page_title("🌊 Hydraulics & Power")
    d = design_calc()
    if not d:
        st.warning("Complete the RO Design page first.")
        return
    with card("Pump efficiencies (IMSDesign defaults)", "⚙️"):
        c = st.columns(3)
        with c[0]:
            w_number("Pump efficiency (%)", "eff_pump", 87.0, min_value=10.0, max_value=100.0)
        with c[1]:
            w_number("Motor efficiency (%)", "eff_motor", 95.0, min_value=10.0, max_value=100.0)
        with c[2]:
            w_number("VFD efficiency (%)", "eff_vfd", 97.0, min_value=10.0, max_value=100.0)
    d = design_calc()
    pu = ss.get("pressure_unit", "psi")
    k = 1 / PSI if pu == "bar" else 1.0
    with card("Hydraulic profile", "📐"):
        for e in d["pl"]:
            n, pdx = e["n"], e["calc"]
            sub(f"Pass {n}")
            tiles([("Feed pressure", f"{pdx['pf'] * k:.2f} {pu}"), ("Average NDP", f"{pdx['ndp'] * k:.2f} {pu}"),
                   ("Avg osmotic pressure", f"{pdx['pi_avg'] * k:.2f} {pu}"), ("Total ΔP (feed–conc)", f"{pdx['dp_total'] * k:.2f} {pu}"),
                   ("Fouling factor / TCF", f"{pdx['ff']:.3f} / {pdx['tcf']:.3f}"), ("Average flux", f"{pdx['flux']:.2f} gfd")])
            show_df(pd.DataFrame([{"Stage": r["stage"], "Inlet pressure": round(r["p_in"] * k, 2), "ΔP stage": round(r["dp_stage"] * k, 2),
                                   "ΔP / element": round(r["dp_el"] * k, 2), "Feed / vessel (gpm)": round(r["feed_v"], 1)} for r in pdx["rows"]]), hide_index=True)
    with card("Power calculation", "⚡"):
        rows = []
        for e in d["pl"]:
            n, pdx = e["n"], e["calc"]
            if pdx:
                rows.append({"Pass": n, "Pump pressure (psi)": round(pdx["pf"], 1), "Pump flow (gpm)": round(pdx["f"], 1),
                             "Power (kW)": round(pdx["kw"], 1), "BHP": round(pdx["bhp"], 1)})
        show_df(pd.DataFrame(rows), hide_index=True)
        tiles([("Total pumping power", f"{d['power_kw']:.1f} kW"), ("Specific energy", f"{d['spec_kwh_kgal']:.2f} kWh/kgal"),
               ("Specific energy", f"{d['spec_kwh_m3']:.3f} kWh/m³"), ("Plant product", f"{d['q'] * GPM:.1f} gpm · {d['q']:.1f} m³/h")])
        st.caption("Power = flow × pressure ÷ (1714 × pump × motor × VFD efficiency); specific energy per kgal of plant product.")
    with card("Pressure model", "ℹ️"):
        st.caption("Feed pressure = NDP + average osmotic pressure + permeate pressure + ½ × vessel pressure drop. NDP = flux ÷ (A × TCF × fouling factor). "
                   "Permeability A and element ΔP are type-typical unless the membrane is marked calibrated on the Library page.")


# =====================================================
# VIEW: WATER QUALITY
# =====================================================
def view_quality():
    page_title("✅ Treated Water Quality")
    d = design_calc()
    if not d:
        st.warning("Complete the RO Design page first.")
        return
    pt = post_treatment(d)
    with card("Product water", "💎"):
        tiles([("Product TDS", f"{d['tds_product']:.2f} mg/L"), ("Product pH", f"{d['product_ph']:.2f}"),
               ("Conductivity", f"{comp_cond(d['product']):.2f} µS/cm"), ("Product boron", f"{d['product']['boron']:.3f} mg/L"),
               ("Product silica", f"{d['product']['sio2']:.3f} mg/L"), ("Product CO₂", f"{d['product']['co2']:.2f} mg/L")])
        if pt["any"]:
            tiles([("After post-treatment: pH", f"{pt['ph']:.2f}"), ("TDS", f"{pt['tds']:.2f} mg/L"), ("LSI", f"{pt['lsi']:+.2f}")])
    with card("Water quality by stream (mg/L)", "📋"):
        show_df(quality_table(d), hide_index=True)
        st.caption("Permeate = salt passage × log-mean feed–concentrate concentration (passage grows with membrane age); CO₂ passes with a passage of 0.88.")
    with card("Stage concentrates", "🧱"):
        for e in d["pl"]:
            sub(f"Pass {e['n']}")
            rows = []
            for r, comp in zip(e["calc"]["rows"], e["stage_conc"]):
                rows.append({"Stage": r["stage"], "Concentrate flow (gpm)": round(r["conc"], 1), "TDS (mg/L)": round(comp_tds(comp), 1),
                             "Osmotic pressure (psi)": round(comp_osm_bar(comp, d["t"]) * PSI, 1)})
            show_df(pd.DataFrame(rows), hide_index=True)


# =====================================================
# VIEW: REPORT
# =====================================================
def render_ro_effluent(d):
    e = effluent_summary(d)
    q = e["q"]
    k = GPM if ss.get("flow_unit") == "gpm" else 1.0
    fu = "gpm" if ss.get("flow_unit") == "gpm" else "m³/h"
    target = _f("target_tds", 0.0)
    tds_cls = "" if target <= 0 else ("good" if q["prod"]["tds"] <= target else "warn")
    with card("Treated Water after RO (Product & Concentrate)", "💎"):
        sub("Flows")
        tiles([("Raw feed", f"{e['flow_raw'] * k:.2f} {fu}"), ("Product (permeate)", f"{e['flow_prod'] * k:.2f} {fu}"),
               ("Concentrate (reject)", f"{e['flow_conc'] * k:.2f} {fu}"), ("Overall recovery", f"{e['rec']:.1f} %")])
        sub("Product (effluent) quality")
        tiles([("Product TDS", f"{q['prod']['tds']:.2f} mg/L", tds_cls) if tds_cls else ("Product TDS", f"{q['prod']['tds']:.2f} mg/L"),
               ("pH", f"{q['prod']['ph']:.2f}"), ("Conductivity", f"{q['prod']['cond']:.2f} µS/cm"),
               ("Hardness", f"{q['prod']['hardness']:.2f} mg/L CaCO₃"), ("Alkalinity", f"{q['prod']['alk']:.2f} mg/L CaCO₃"),
               ("Boron", f"{e['prod']['boron']:.3f} mg/L"), ("Silica", f"{e['prod']['sio2']:.3f} mg/L"),
               ("CO₂", f"{e['prod']['co2']:.2f} mg/L"), ("TDS rejection", f"{e['tds_rej']:.2f} %")])
        if target > 0:
            st.caption(f"Target product TDS: {target:.1f} mg/L - " + ("met." if q["prod"]["tds"] <= target else "NOT met."))
        if e["post"]:
            sub("After post-treatment")
            pt = e["post"]
            tiles([("pH", f"{pt['ph']:.2f}"), ("TDS", f"{pt['tds']:.2f} mg/L"), ("Alkalinity", f"{pt['alk']:.1f} mg/L CaCO₃"),
                   ("Hardness", f"{pt['hardness']:.1f} mg/L CaCO₃"), ("LSI", f"{pt['lsi']:+.2f}")])
        sub("Concentrate (reject)")
        tiles([("TDS", f"{q['conc']['tds']:.1f} mg/L"), ("pH", f"{q['conc']['ph']:.2f}"), ("Conductivity", f"{q['conc']['cond']:.0f} µS/cm"),
               ("Osmotic pressure", f"{e['osm_conc_psi']:.1f} psi"), ("Concentration factor (pass 1)", f"{e['cf']:.2f}"),
               ("LSI", f"{e['lsi_conc']:+.2f}", "good" if e["lsi_conc"] <= 0 else "warn")]
              + [(f"{n} saturation", f"{v:.0f} %", "bad" if v > 100 else "good") for n, v in e["sat_conc"].items() if v >= 1])
        sub("Raw water vs RO product vs concentrate")
        post_col = "After post-treatment"
        table = []
        for r in effluent_rows(e):
            row = {"Parameter": r["param"], "Unit": r["unit"], "Raw water": fmt(r["raw"], 3), "RO product": fmt(r["prod"], 3),
                   "Rejection (%)": "-" if r["rej"] is None else fmt(r["rej"], 2)}
            if e["post"]:
                row[post_col] = "-" if r["post"] is None else fmt(r["post"], 3)
            row["Concentrate"] = fmt(r["conc"], 3)
            row["Conc. factor"] = "-" if r["factor"] is None else fmt(r["factor"], 2)
            table.append(row)
        show_df(pd.DataFrame(table), hide_index=True)
        st.caption("Product = salt passage × log-mean feed–concentrate concentration (passage grows with membrane age); concentrate = mass balance of the "
                   "stage concentrates (the pass-2 concentrate is added when it is not recycled). Rejection is against the raw water.")


def view_report():
    page_title("📄 Report")
    d = design_calc()
    checks = run_checks(d)
    with card("Get Report", "🖨"):
        status_banner(checks, "Design")
        c = st.columns([1.3, 1.3, 2])
        try:
            pdf = build_pdf_report()
            with c[0]:
                st.download_button("📄 Download PDF report", data=pdf, file_name=f"{_safe_name(ss.get('project_name', 'RO'))}_Report.pdf",
                                   mime="application/pdf", key="ui_report_pdf")
            with c[1]:
                if st.button("💾 Save PDF in project folder", key="ui_pdf_folder"):
                    try:
                        p = project_path().parent / f"{_safe_name(ss.get('project_name'))}_Report.pdf"
                        p.parent.mkdir(parents=True, exist_ok=True)
                        p.write_bytes(pdf)
                        st.success(f"Saved: {p}")
                    except OSError as e:
                        st.error(f"Could not save: {e}")
        except Exception as e:
            st.error(f"Could not build the PDF report: {e}")
    if d:
        render_ro_effluent(d)
    with card("Design cautions", "⚠️"):
        checklist(checks)
    if d:
        with card("Report contents", "📋"):
            tiles([("Project", ss.get("project_name", "")), ("Membrane", f"{d['m1']['vendor']} {d['m1']['model']}"),
                   ("Passes", d["passes"]), ("Product flow", f"{d['q']:.2f} m³/h"), ("Specific energy", f"{d['spec_kwh_kgal']:.2f} kWh/kgal")])


# =====================================================
# VIEW: LIBRARY
# =====================================================
def _editor(df, key, **kw):
    try:
        return st.data_editor(df, width="stretch", key=key, hide_index=True, **kw)
    except TypeError:
        return st.data_editor(df, use_container_width=True, key=key, hide_index=True, **kw)


def view_library():
    page_title("📚 Membrane Library")
    lib = load_library()
    st.warning("Your original 13 membranes keep their database values (**permeability a_w and element dP are type-typical**, ESPA2 MAX is calibrated to an IMSDesign run). "
               "The DuPont FilmTec, Nitto Hydranautics and LG Chem models added after them use the manufacturers' published **area, salt rejection and standard-test flow**; "
               "their **permeability is scaled from that test flow** to the ESPA2 MAX calibration and element dP is the generic calibration value. "
               "Check the notes column and enter datasheet / projection-software values before relying on the pressures. New vendors are added by typing a new vendor name.")
    with card("Membranes (add rows to add membranes / vendors)", "🧫"):
        edited = _editor(pd.DataFrame(lib["membranes"])[MEM_COLUMNS], "ui_mem_editor", num_rows="dynamic")
        st.caption("a_w = permeability (gfd/psi at 25 °C, new membrane) · dp_ref = element pressure drop at 50 gpm (psi) · max_pressure in psi.")
    with card("Vendor guidelines", "🏭"):
        vdf = pd.DataFrame([{"vendor": v, **p} for v, p in lib["vendors"].items()])
        vedit = _editor(vdf, "ui_vendor_editor", num_rows="dynamic")
        st.caption("Per vendor: max feed gpm and min concentrate gpm per vessel, max element / vessel ΔP (psi), max lead-element recovery (%), "
                   "feed temperature, pH range, free chlorine, SDI, and a flux scale (1.0 = the table below).")
    with card("Recommended maximum flux (gfd) by water type", "💧"):
        fdf = pd.DataFrame([{"water_type": w, "pass1_gfd": v[0], "pass2_gfd": v[1]} for w, v in lib["flux"].items()])
        fedit = _editor(fdf, "ui_flux_editor")
    with card("Antiscalants", "🧴"):
        aedit = _editor(pd.DataFrame(lib["antiscalants"]), "ui_as_editor", num_rows="dynamic")
    c = st.columns(4)
    with c[0]:
        if st.button("💾 Save library", key="ui_lib_save"):
            try:
                mems = [_clean_membrane(r) for r in edited.to_dict("records") if str(r.get("vendor") or "").strip() and str(r.get("model") or "").strip()]
                vendors = {}
                for r in vedit.to_dict("records"):
                    name = str(r.get("vendor") or "").strip()
                    if name:
                        full = dict(VENDOR_DEFAULTS)
                        for k in VENDOR_DEFAULTS:
                            if k in r and r[k] == r[k] and r[k] is not None:
                                full[k] = r[k]
                        vendors[name] = full
                flux = {str(r["water_type"]): [float(r["pass1_gfd"]), float(r["pass2_gfd"])] for r in fedit.to_dict("records") if r.get("water_type")}
                anti = [{"product": str(r["product"]), "vendor": str(r.get("vendor") or ""), "base_dose": float(r.get("base_dose") or 3.0),
                         "application": str(r.get("application") or "")} for r in aedit.to_dict("records") if r.get("product")]
                save_library(mems, vendors, anti, flux)
                st.success(f"Library saved ({len(mems)} membranes).")
            except Exception as e:
                st.error(f"Could not save: {e}")
    with c[1]:
        if st.button("↩ Reset to built-in", key="ui_lib_reset"):
            try:
                LIB_FILE.unlink()
            except OSError:
                pass
            st.success("Built-in library restored - reload the page.")
    with c[2]:
        st.download_button("⬇ Export library", data=json.dumps({**lib, "builtin_ver": BUILTIN_VER}, indent=2), file_name="membrane_library.json", mime="application/json", key="ui_lib_dl")
    with c[3]:
        up = st.file_uploader("Import library (.json)", type=["json"], key="ui_lib_up", label_visibility="collapsed")
        if up is not None and st.button("Import", key="ui_lib_import"):
            try:
                dd = json.loads(up.getvalue().decode("utf-8"))
                save_library(dd.get("membranes", []), dd.get("vendors", {}), dd.get("antiscalants", []), dd.get("flux", {}), ver=int(dd.get("builtin_ver", 1)))
                st.success("Library imported - reload the page.")
            except Exception as e:
                st.error(f"Invalid library file: {e}")


# =====================================================
# DISPATCH
# =====================================================
{"Projects": view_projects, "Feed Water": view_feed, "RO Design": view_design, "Chemicals": view_chem,
 "Hydraulics & Power": view_hyd, "Water Quality": view_quality, "Report": view_report, "Library": view_library}[main]()

# =====================================================
# AUTO-SAVE + HEADER
# =====================================================
save_clicked = ss.pop("_save_clicked", False)
autosave_disk = ss.get("autosave_disk", True)
body_hash = hashlib.md5(json.dumps(collect_project(), sort_keys=True, default=str).encode()).hexdigest()
target = str(project_path())
if save_clicked or (autosave_disk and (body_hash != ss.get("_last_hash") or target != ss.get("_last_path"))):
    if save_to_disk() is not None:
        ss["_last_hash"] = body_hash

if ss.get("_disk_error"):
    status_txt, chip_cls = "⚠ not saved to folder", "chip"
else:
    status_txt = f"✅ Auto-saved {ss['_last_saved_at']}" if ss.get("_last_saved_at") else "Auto-save ready"
    chip_cls = "chip ok"
try:
    _d = design_calc()
    _lvl = overall(run_checks(_d)) if _d else None
except Exception:
    _lvl = None
hdr_ph.markdown(
    f'<div class="mdw"><div class="hdr"><div><div class="hdr-title">{APP_TITLE}</div>'
    f'<div class="hdr-sub">RO design · membranes · chemicals · power</div></div>'
    f'</div></div>',
    unsafe_allow_html=True)

_lvl_txt = {"ok": "✅ Design OK", "warn": "⚠ Check cautions", "bad": "❌ Red cautions"}.get(_lvl, "")
side_status.markdown(
    f'<div class="mdw"><div class="sb-status"><b>{hesc(str(ss.get("project_name", "")))}</b><br>{status_txt}'
    f'{"<br>" + _lvl_txt if _lvl_txt else ""}</div></div>', unsafe_allow_html=True)