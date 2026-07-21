"""
KUNDALI — Vedic birth-chart engine (Python / Streamlit port)
-------------------------------------------------------------
- City-name lookup (built-in gazetteer)
- Combined chart: birth (ivory) + live transits (red)
- Houses fixed to the birth lagna, degrees on every graha

Run with:
    pip install streamlit pandas
    streamlit run kundali_app.py
"""

import math
import hashlib
import hmac
import os
import re
import secrets
import sqlite3
import time
from datetime import datetime, timedelta, date, time as dtime

import streamlit as st
import pandas as pd

# ============================================================
# ASTRONOMY ENGINE  (direct port of the JS math, same formulas)
# ============================================================

D2R = math.pi / 180


def norm360(x: float) -> float:
    return (x % 360 + 360) % 360


def julian_day(y: int, m: int, d: int, ut_hours: float) -> float:
    if m <= 2:
        y -= 1
        m += 12
    A = math.floor(y / 100)
    B = 2 - A + math.floor(A / 4)
    return (
        math.floor(365.25 * (y + 4716))
        + math.floor(30.6001 * (m + 1))
        + d
        + B
        - 1524.5
        + ut_hours / 24
    )


def sun_longitude(jd: float) -> float:
    T = (jd - 2451545.0) / 36525
    L0 = 280.46646 + 36000.76983 * T + 0.0003032 * T * T
    M = (357.52911 + 35999.05029 * T - 0.0001537 * T * T) * D2R
    C = (
        (1.914602 - 0.004817 * T - 0.000014 * T * T) * math.sin(M)
        + (0.019993 - 0.000101 * T) * math.sin(2 * M)
        + 0.000289 * math.sin(3 * M)
    )
    return norm360(L0 + C)


def moon_longitude(jd: float) -> float:
    T = (jd - 2451545.0) / 36525
    Lp = 218.3164477 + 481267.88123421 * T
    D = (297.8501921 + 445267.1114034 * T) * D2R
    M = (357.5291092 + 35999.0502909 * T) * D2R
    Mp = (134.9633964 + 477198.8675055 * T) * D2R
    F = (93.272095 + 483202.0175233 * T) * D2R
    lon = (
        Lp
        + 6.288774 * math.sin(Mp)
        + 1.274027 * math.sin(2 * D - Mp)
        + 0.658314 * math.sin(2 * D)
        + 0.213618 * math.sin(2 * Mp)
        - 0.185116 * math.sin(M)
        - 0.114332 * math.sin(2 * F)
        + 0.058793 * math.sin(2 * D - 2 * Mp)
        + 0.057066 * math.sin(2 * D - M - Mp)
        + 0.053322 * math.sin(2 * D + Mp)
        + 0.045758 * math.sin(2 * D - M)
        - 0.040923 * math.sin(M - Mp)
        - 0.03472 * math.sin(D)
        - 0.030383 * math.sin(M + Mp)
        + 0.015327 * math.sin(2 * D - 2 * F)
        - 0.012528 * math.sin(Mp + 2 * F)
        + 0.01098 * math.sin(Mp - 2 * F)
    )
    return norm360(lon)


def mean_node(jd: float) -> float:
    T = (jd - 2451545.0) / 36525
    return norm360(125.04452 - 1934.136261 * T)


ELEMENTS = {
    "Mercury": [0.38709927, 0.20563593, 7.00497902, 252.2503235, 77.45779628, 48.33076593,
                0.00000037, 0.00001906, -0.00594749, 149472.67411175, 0.16047689, -0.12534081],
    "Venus":   [0.72333566, 0.00677672, 3.39467605, 181.9790995, 131.60246718, 76.67984255,
                0.0000039, -0.00004107, -0.0007889, 58517.81538729, 0.00268329, -0.27769418],
    "Earth":   [1.00000261, 0.01671123, -0.00001531, 100.46457166, 102.93768193, 0.0,
                0.00000562, -0.00004392, -0.01294668, 35999.37244981, 0.32327364, 0.0],
    "Mars":    [1.52371034, 0.0933941, 1.84969142, -4.55343205, -23.94362959, 49.55953891,
                0.00001847, 0.00007882, -0.00813131, 19140.30268499, 0.44441088, -0.29257343],
    "Jupiter": [5.202887, 0.04838624, 1.30439695, 34.39644051, 14.72847983, 100.47390909,
                -0.00011607, -0.00013253, -0.00183714, 3034.74612775, 0.21252668, 0.20469106],
    "Saturn":  [9.53667594, 0.05386179, 2.48599187, 49.95424423, 92.59887831, 113.66242448,
                -0.0012506, -0.00050991, 0.00193609, 1222.49362201, -0.41897216, -0.28867794],
}


def helio_position(name: str, jd: float):
    T = (jd - 2451545.0) / 36525
    e0 = ELEMENTS[name]
    a = e0[0] + e0[6] * T
    ec = e0[1] + e0[7] * T
    I = (e0[2] + e0[8] * T) * D2R
    L = e0[3] + e0[9] * T
    wbar = e0[4] + e0[10] * T
    OmD = e0[5] + e0[11] * T
    Om = OmD * D2R
    w = (wbar - OmD) * D2R
    M = norm360(L - wbar) * D2R
    E = M + ec * math.sin(M)
    for _ in range(8):
        E = E - (E - ec * math.sin(E) - M) / (1 - ec * math.cos(E))
    xp = a * (math.cos(E) - ec)
    yp = a * math.sqrt(1 - ec * ec) * math.sin(E)
    cw, sw = math.cos(w), math.sin(w)
    cO, sO = math.cos(Om), math.sin(Om)
    ci, si = math.cos(I), math.sin(I)
    x = (cw * cO - sw * sO * ci) * xp + (-sw * cO - cw * sO * ci) * yp
    y = (cw * sO + sw * cO * ci) * xp + (-sw * sO + cw * cO * ci) * yp
    z = sw * si * xp + cw * si * yp
    return x, y, z


def geo_longitude(name: str, jd: float) -> float:
    px, py, _ = helio_position(name, jd)
    ex, ey, _ = helio_position("Earth", jd)
    return norm360(math.atan2(py - ey, px - ex) / D2R)


AYAN_J2000 = 23.85311


def ayanamsa(jd: float) -> float:
    return AYAN_J2000 + ((jd - 2451545.0) / 365.25) * 0.013972


def ascendant(jd: float, lat_deg: float, lon_deg: float) -> float:
    T = (jd - 2451545.0) / 36525
    gmst = norm360(280.46061837 + 360.98564736629 * (jd - 2451545.0) + 0.000387933 * T * T)
    ramc = norm360(gmst + lon_deg) * D2R
    eps = (23.4392911 - 0.013004 * T) * D2R
    phi = lat_deg * D2R
    asc = math.atan2(
        math.cos(ramc),
        -(math.sin(ramc) * math.cos(eps) + math.tan(phi) * math.sin(eps)),
    )
    return norm360(asc / D2R)


def navamsa_sign(lon_sid: float) -> int:
    """Standard D9 (navamsa) sign for a sidereal longitude: movable signs start their
    navamsa count from themselves, fixed signs from the 9th, dual signs from the 5th."""
    sign = math.floor(lon_sid / 30)
    in_sign = lon_sid - sign * 30
    nav_num = math.floor(in_sign / (10.0 / 3.0))  # 0-8
    if sign % 3 == 0:      # movable: Ar, Cn, Li, Cp
        start = sign
    elif sign % 3 == 1:    # fixed: Ta, Le, Sc, Aq -> 9th from itself
        start = (sign + 8) % 12
    else:                  # dual: Ge, Vi, Sg, Pi -> 5th from itself
        start = (sign + 4) % 12
    return int((start + nav_num) % 12)


def sunrise_utc_hours(y: int, mo: int, dd: int, lat: float, lon: float) -> float:
    """Approximate sunrise time in UT decimal hours for a given calendar date/place
    (equation-of-time not applied — consistent with this engine's other low-precision math)."""
    jd_noon = julian_day(y, mo, dd, 12.0)
    sun_trop = sun_longitude(jd_noon)
    decl = declination(sun_trop, 0.0, jd_noon)
    lat_r, decl_r = lat * D2R, decl * D2R
    cosH = -math.tan(lat_r) * math.tan(decl_r)
    cosH = max(-1.0, min(1.0, cosH))
    H = math.acos(cosH) / D2R
    return 12.0 - lon / 15.0 - H / 15.0


# ============================================================
# DIVISIONAL (VARGA) CHARTS — standard Parashari reckoning rules.
# Each rule maps (rāśi index 0-11, segment index within that rāśi) -> resulting sign.
# ============================================================

VARGA_DIVISORS = {
    "D1": 1, "D2": 2, "D3": 3, "D4": 4, "D6": 6, "D7": 7, "D9": 9,
    "D10": 10, "D11": 11, "D12": 12, "D16": 16, "D20": 20, "D24": 24,
    "D27": 27, "D60": 60,
}
VARGA_OPTIONS = ["D1", "D2", "D3", "D4", "D6", "D7", "D9", "D10", "D11",
                  "D12", "D16", "D20", "D24", "D27", "D60"]


def _varga_D2(sign, seg):  # Hora: alternates Leo/Cancer
    odd = sign % 2 == 0  # Ar,Ge,Le,Li,Sg,Aq
    if odd:
        return 4 if seg == 0 else 3
    return 3 if seg == 0 else 4


def _varga_D3(sign, seg):
    return (sign + seg * 4) % 12


def _varga_D4(sign, seg):
    return (sign + seg * 3) % 12


def _varga_D6(sign, seg):
    start = 0 if sign % 2 == 0 else 6
    return (start + seg) % 12


def _varga_D7(sign, seg):
    start = sign if sign % 2 == 0 else (sign + 6) % 12
    return (start + seg) % 12


def _varga_D9(sign, seg):
    if sign % 3 == 0:
        start = sign
    elif sign % 3 == 1:
        start = (sign + 8) % 12
    else:
        start = (sign + 4) % 12
    return (start + seg) % 12


def _varga_D10(sign, seg):
    start = sign if sign % 2 == 0 else (sign + 8) % 12
    return (start + seg) % 12


def _varga_D11(sign, seg):
    return ((sign + 11) + seg) % 12


def _varga_D12(sign, seg):
    return (sign + seg) % 12


def _varga_D16(sign, seg):
    m = sign % 3
    start = 0 if m == 0 else (4 if m == 1 else 8)
    return (start + seg) % 12


def _varga_D20(sign, seg):
    m = sign % 3
    start = 0 if m == 0 else (8 if m == 1 else 4)
    return (start + seg) % 12


def _varga_D24(sign, seg):
    start = 4 if sign % 2 == 0 else 3
    return (start + seg) % 12


def _varga_D27(sign, seg):
    elem = sign % 4
    start = [0, 3, 6, 9][elem]
    return (start + seg) % 12


def _varga_D60(sign, seg):
    return (sign * 2 + seg) % 12


_VARGA_FUNCS = {
    2: _varga_D2, 3: _varga_D3, 4: _varga_D4, 6: _varga_D6, 7: _varga_D7,
    9: _varga_D9, 10: _varga_D10, 11: _varga_D11, 12: _varga_D12,
    16: _varga_D16, 20: _varga_D20, 24: _varga_D24, 27: _varga_D27, 60: _varga_D60,
}


def varga_sign(lon_sid: float, varga_key: str):
    """Returns (resulting_sign 0-11, synthetic degree-in-sign 0-30) for a sidereal
    longitude in the given divisional chart. The degree is the fractional position
    within the division scaled back up to 30°, so the varga chart still shows a
    coherent per-graha degree the way the reference site does."""
    divisor = VARGA_DIVISORS[varga_key]
    sign = math.floor(lon_sid / 30)
    in_sign = lon_sid - sign * 30
    if divisor == 1:
        return sign, in_sign
    seg_size = 30.0 / divisor
    seg = min(int(math.floor(in_sign / seg_size)), divisor - 1)
    frac = (in_sign - seg * seg_size) / seg_size
    result_sign = _VARGA_FUNCS[divisor](sign, seg)
    return result_sign, frac * 30


def make_varga_bodies(bodies, varga_key: str):
    """Re-maps a list of body dicts (as produced by compute_chart) onto a divisional
    chart, replacing sign/inSign but leaving key/retro/combust/etc. untouched."""
    if varga_key == "D1":
        return bodies
    out = []
    for b in bodies:
        vsign, vdeg = varga_sign(b["lon"], varga_key)
        nb = dict(b)
        nb["sign"] = vsign
        nb["inSign"] = vdeg
        out.append(nb)
    return out


# ============================================================
# STATIC TABLES (same as the original)
# ============================================================

SIGNS = ["Meṣa", "Vṛṣabha", "Mithuna", "Karka", "Siṁha", "Kanyā", "Tulā", "Vṛścika",
         "Dhanu", "Makara", "Kumbha", "Mīna"]

NAKSHATRAS = ["Aśvinī", "Bharaṇī", "Kṛttikā", "Rohiṇī", "Mṛgaśirā", "Ārdrā", "Punarvasu",
              "Puṣya", "Āśleṣā", "Maghā", "Pūrva Phalgunī", "Uttara Phalgunī", "Hasta",
              "Citrā", "Svātī", "Viśākhā", "Anurādhā", "Jyeṣṭhā", "Mūla", "Pūrva Āṣāḍhā",
              "Uttara Āṣāḍhā", "Śravaṇa", "Dhaniṣṭhā", "Śatabhiṣā", "Pūrva Bhādrapadā",
              "Uttara Bhādrapadā", "Revatī"]

TITHIS = ["Pratipadā", "Dvitīyā", "Tṛtīyā", "Caturthī", "Pañcamī", "Ṣaṣṭhī", "Saptamī",
          "Aṣṭamī", "Navamī", "Daśamī", "Ekādaśī", "Dvādaśī", "Trayodaśī", "Caturdaśī"]

YOGAS = ["Viṣkambha", "Prīti", "Āyuṣmān", "Saubhāgya", "Śobhana", "Atigaṇḍa", "Sukarma",
         "Dhṛti", "Śūla", "Gaṇḍa", "Vṛddhi", "Dhruva", "Vyāghāta", "Harṣaṇa", "Vajra",
         "Siddhi", "Vyatīpāta", "Varīyān", "Parigha", "Śiva", "Siddha", "Sādhya", "Śubha",
         "Śukla", "Brahma", "Indra", "Vaidhṛti"]

KARANA_MOVABLE = ["Bava", "Bālava", "Kaulava", "Taitila", "Gara", "Vaṇija", "Viṣṭi"]

VARAS = ["Ravivāra (Sun)", "Somavāra (Mon)", "Maṅgalavāra (Tue)", "Budhavāra (Wed)",
         "Guruvāra (Thu)", "Śukravāra (Fri)", "Śanivāra (Sat)"]

DASHA_LORDS = ["Ketu", "Śukra (Ve)", "Sūrya (Su)", "Candra (Mo)", "Maṅgala (Ma)",
               "Rāhu", "Guru (Jp)", "Śani (Sa)", "Budha (Me)"]
DASHA_YEARS = [7, 20, 6, 10, 7, 18, 16, 19, 17]

DASHA_LORD_SHORT = ["Ke", "Ve", "Su", "Mo", "Ma", "Ra", "Jp", "Sa", "Me"]

SIGN_ABBR = ["Ar", "Ta", "Ge", "Cn", "Le", "Vi", "Li", "Sc", "Sg", "Cp", "Aq", "Pi"]

NAK_ABBR = ["Aśw", "Bha", "Krt", "Roh", "Mrg", "Ard", "Pun", "Pus", "Āśl", "Mag", "PPh",
            "UPh", "Has", "Cit", "Swa", "Vis", "Anu", "Jye", "Mūl", "PAs", "UAs", "Śra",
            "Dha", "Śat", "PBh", "UBh", "Rev"]

COMBUSTION_ORB = {"Ma": 17, "Me": 14, "Jp": 11, "Ve": 10, "Sa": 15}

# the 10 bodies plotted on the diamond/circular charts (special lagnas are table-only)
CORE_KEYS = ["As", "Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa", "Ra", "Ke"]

# name, region, lat, lon, tz(hours)
CITIES = [
    ("Bathinda", "Punjab, India", 30.21, 74.95, 5.5),
    ("Amritsar", "Punjab, India", 31.63, 74.87, 5.5),
    ("Ludhiana", "Punjab, India", 30.9, 75.85, 5.5),
    ("Jalandhar", "Punjab, India", 31.33, 75.58, 5.5),
    ("Patiala", "Punjab, India", 30.34, 76.39, 5.5),
    ("Moga", "Punjab, India", 30.82, 75.17, 5.5),
    ("Firozpur", "Punjab, India", 30.93, 74.62, 5.5),
    ("Sangrur", "Punjab, India", 30.25, 75.84, 5.5),
    ("Barnala", "Punjab, India", 30.38, 75.55, 5.5),
    ("Mansa", "Punjab, India", 29.99, 75.4, 5.5),
    ("Muktsar", "Punjab, India", 30.47, 74.52, 5.5),
    ("Faridkot", "Punjab, India", 30.67, 74.76, 5.5),
    ("Abohar", "Punjab, India", 30.14, 74.2, 5.5),
    ("Chandigarh", "India", 30.73, 76.78, 5.5),
    ("New Delhi", "India", 28.61, 77.21, 5.5),
    ("Mumbai", "Maharashtra, India", 19.08, 72.88, 5.5),
    ("Kolkata", "West Bengal, India", 22.57, 88.36, 5.5),
    ("Chennai", "Tamil Nadu, India", 13.08, 80.27, 5.5),
    ("Bengaluru", "Karnataka, India", 12.97, 77.59, 5.5),
    ("Hyderabad", "Telangana, India", 17.39, 78.49, 5.5),
    ("Pune", "Maharashtra, India", 18.52, 73.86, 5.5),
    ("Ahmedabad", "Gujarat, India", 23.02, 72.57, 5.5),
    ("Surat", "Gujarat, India", 21.17, 72.83, 5.5),
    ("Jaipur", "Rajasthan, India", 26.91, 75.79, 5.5),
    ("Jodhpur", "Rajasthan, India", 26.24, 73.02, 5.5),
    ("Udaipur", "Rajasthan, India", 24.58, 73.71, 5.5),
    ("Lucknow", "Uttar Pradesh, India", 26.85, 80.95, 5.5),
    ("Kanpur", "Uttar Pradesh, India", 26.45, 80.33, 5.5),
    ("Varanasi", "Uttar Pradesh, India", 25.32, 82.97, 5.5),
    ("Prayagraj", "Uttar Pradesh, India", 25.44, 81.85, 5.5),
    ("Agra", "Uttar Pradesh, India", 27.18, 78.01, 5.5),
    ("Meerut", "Uttar Pradesh, India", 28.98, 77.71, 5.5),
    ("Ghaziabad", "Uttar Pradesh, India", 28.67, 77.42, 5.5),
    ("Noida", "Uttar Pradesh, India", 28.57, 77.32, 5.5),
    ("Gorakhpur", "Uttar Pradesh, India", 26.76, 83.37, 5.5),
    ("Gurugram", "Haryana, India", 28.46, 77.03, 5.5),
    ("Faridabad", "Haryana, India", 28.41, 77.31, 5.5),
    ("Rohtak", "Haryana, India", 28.9, 76.61, 5.5),
    ("Hisar", "Haryana, India", 29.15, 75.72, 5.5),
    ("Karnal", "Haryana, India", 29.69, 76.99, 5.5),
    ("Ambala", "Haryana, India", 30.38, 76.78, 5.5),
    ("Sirsa", "Haryana, India", 29.53, 75.03, 5.5),
    ("Shimla", "Himachal Pradesh, India", 31.1, 77.17, 5.5),
    ("Jammu", "J&K, India", 32.73, 74.87, 5.5),
    ("Srinagar", "J&K, India", 34.08, 74.8, 5.5),
    ("Dehradun", "Uttarakhand, India", 30.32, 78.03, 5.5),
    ("Haridwar", "Uttarakhand, India", 29.95, 78.16, 5.5),
    ("Bhopal", "Madhya Pradesh, India", 23.26, 77.41, 5.5),
    ("Indore", "Madhya Pradesh, India", 22.72, 75.86, 5.5),
    ("Gwalior", "Madhya Pradesh, India", 26.22, 78.18, 5.5),
    ("Ujjain", "Madhya Pradesh, India", 23.18, 75.78, 5.5),
    ("Nagpur", "Maharashtra, India", 21.15, 79.09, 5.5),
    ("Nashik", "Maharashtra, India", 19.99, 73.79, 5.5),
    ("Patna", "Bihar, India", 25.59, 85.14, 5.5),
    ("Gaya", "Bihar, India", 24.78, 85.0, 5.5),
    ("Ranchi", "Jharkhand, India", 23.34, 85.31, 5.5),
    ("Raipur", "Chhattisgarh, India", 21.25, 81.63, 5.5),
    ("Bhubaneswar", "Odisha, India", 20.3, 85.82, 5.5),
    ("Puri", "Odisha, India", 19.81, 85.83, 5.5),
    ("Guwahati", "Assam, India", 26.14, 91.74, 5.5),
    ("Panaji", "Goa, India", 15.49, 73.83, 5.5),
    ("Kochi", "Kerala, India", 9.93, 76.27, 5.5),
    ("Thiruvananthapuram", "Kerala, India", 8.52, 76.94, 5.5),
    ("Coimbatore", "Tamil Nadu, India", 11.02, 76.96, 5.5),
    ("Madurai", "Tamil Nadu, India", 9.93, 78.12, 5.5),
    ("Visakhapatnam", "Andhra Pradesh, India", 17.69, 83.22, 5.5),
    ("Vijayawada", "Andhra Pradesh, India", 16.51, 80.65, 5.5),
    ("Tirupati", "Andhra Pradesh, India", 13.63, 79.42, 5.5),
    ("Mysuru", "Karnataka, India", 12.3, 76.64, 5.5),
    ("Rajkot", "Gujarat, India", 22.3, 70.8, 5.5),
    ("Vadodara", "Gujarat, India", 22.31, 73.18, 5.5),
    ("Kathmandu", "Nepal", 27.72, 85.32, 5.75),
    ("Colombo", "Sri Lanka", 6.93, 79.85, 5.5),
    ("Dhaka", "Bangladesh", 23.81, 90.41, 6),
    ("Karachi", "Pakistan", 24.86, 67.01, 5),
    ("Lahore", "Pakistan", 31.55, 74.34, 5),
    ("Dubai", "UAE", 25.2, 55.27, 4),
    ("Abu Dhabi", "UAE", 24.45, 54.38, 4),
    ("Doha", "Qatar", 25.29, 51.53, 3),
    ("Riyadh", "Saudi Arabia", 24.71, 46.68, 3),
    ("Singapore", "Singapore", 1.35, 103.82, 8),
    ("Kuala Lumpur", "Malaysia", 3.14, 101.69, 8),
    ("Bangkok", "Thailand", 13.76, 100.5, 7),
    ("Hong Kong", "China", 22.32, 114.17, 8),
    ("Tokyo", "Japan", 35.68, 139.69, 9),
    ("London", "UK", 51.51, -0.13, 0),
    ("Paris", "France", 48.86, 2.35, 1),
    ("Frankfurt", "Germany", 50.11, 8.68, 1),
    ("New York", "USA", 40.71, -74.01, -5),
    ("Chicago", "USA", 41.88, -87.63, -6),
    ("Houston", "USA", 29.76, -95.37, -6),
    ("Los Angeles", "USA", 34.05, -118.24, -8),
    ("San Francisco", "USA", 37.77, -122.42, -8),
    ("Toronto", "Canada", 43.65, -79.38, -5),
    ("Vancouver", "Canada", 49.28, -123.12, -8),
    ("Sydney", "Australia", -33.87, 151.21, 10),
    ("Melbourne", "Australia", -37.81, 144.96, 10),
    ("Auckland", "New Zealand", -36.85, 174.76, 12),
]


def fmt_deg(x: float) -> str:
    d = math.floor(x)
    m = math.floor((x - d) * 60)
    return f"{d}°{m:02d}′"


def fmt_dms(x: float) -> str:
    """Signed degrees -> D°M'S\" string (handles negative values for latitude/declination)."""
    sign = "-" if x < 0 else ""
    x = abs(x)
    d = math.floor(x)
    rem_m = (x - d) * 60
    m = math.floor(rem_m)
    s = round((rem_m - m) * 60)
    if s == 60:
        s = 0
        m += 1
    if m == 60:
        m = 0
        d += 1
    return f'{sign}{d}°{m}\'{s}"'


def moon_ecliptic_latitude(jd: float) -> float:
    """Low-precision series (Meeus, ch.47) for the Moon's ecliptic latitude, in degrees."""
    T = (jd - 2451545.0) / 36525
    D = (297.8501921 + 445267.1114034 * T) * D2R
    M = (357.5291092 + 35999.0502909 * T) * D2R
    Mp = (134.9633964 + 477198.8675055 * T) * D2R
    F = (93.272095 + 483202.0175233 * T) * D2R
    beta = (
        5.128122 * math.sin(F)
        + 0.280602 * math.sin(Mp + F)
        + 0.277693 * math.sin(Mp - F)
        + 0.173237 * math.sin(2 * D - F)
        + 0.055413 * math.sin(2 * D + F - Mp)
        + 0.046271 * math.sin(2 * D - F - Mp)
        + 0.032573 * math.sin(2 * D + F)
        + 0.017198 * math.sin(2 * Mp + F)
        + 0.009266 * math.sin(2 * D + Mp - F)
        + 0.008822 * math.sin(2 * D - F - 2 * Mp)
        + 0.008216 * math.sin(2 * D - M - F)
        + 0.004324 * math.sin(2 * D - F - 2 * Mp)
    )
    return beta


def geo_ecliptic_lat(name: str, jd: float) -> float:
    px, py, pz = helio_position(name, jd)
    ex, ey, ez = helio_position("Earth", jd)
    gx, gy, gz = px - ex, py - ey, pz - ez
    return math.atan2(gz, math.sqrt(gx * gx + gy * gy)) / D2R


def declination(lon_trop_deg: float, lat_ecl_deg: float, jd: float) -> float:
    """Ecliptic (tropical longitude, latitude) -> equatorial declination, in degrees."""
    T = (jd - 2451545.0) / 36525
    eps = (23.4392911 - 0.013004 * T) * D2R
    lam = lon_trop_deg * D2R
    bet = lat_ecl_deg * D2R
    dec = math.asin(math.sin(bet) * math.cos(eps) + math.cos(bet) * math.sin(eps) * math.sin(lam))
    return dec / D2R


def chara_karaka(degrees_in_sign: dict) -> dict:
    """Classical 8-Kāraka scheme (includes Rāhu with reversed degree, excludes Ketu).
    Ranks by degree-within-sign, highest -> AK ... lowest -> DK."""
    names = ["AK", "AmK", "BK", "MK", "PiK", "PK", "GK", "DK"]
    ranked = sorted(degrees_in_sign.items(), key=lambda kv: kv[1], reverse=True)
    return {key: names[i] for i, (key, _) in enumerate(ranked)}


# ============================================================
# CHART COMPUTATION
# ============================================================

def compute_chart(y: int, mo: int, dd: int, hh: int, mm: int, lat: float, lon: float, tz: float) -> dict:
    ut_hours = hh + mm / 60 - tz
    jd = julian_day(y, mo, dd, ut_hours)
    ayan_date = ayanamsa(jd)

    sun_trop = sun_longitude(jd)
    moon_trop = moon_longitude(jd)
    sun_sid = norm360(sun_trop - ayan_date)
    moon_sid = norm360(moon_trop - ayan_date)
    rahu_sid = norm360(mean_node(jd) - ayan_date)
    ketu_sid = norm360(rahu_sid + 180)

    planet_sid, planet_retro, planet_trop, planet_lat, planet_dec = {}, {}, {}, {}, {}
    for p in ["Mercury", "Venus", "Mars", "Jupiter", "Saturn"]:
        l1 = geo_longitude(p, jd)
        l2 = geo_longitude(p, jd + 0.5)
        planet_sid[p] = norm360(l1 - AYAN_J2000)
        planet_trop[p] = l1
        planet_lat[p] = geo_ecliptic_lat(p, jd)
        planet_dec[p] = declination(l1, planet_lat[p], jd)
        diff = l2 - l1
        if diff > 180:
            diff -= 360
        if diff < -180:
            diff += 360
        planet_retro[p] = diff < 0

    asc_sid = norm360(ascendant(jd, lat, lon) - ayan_date)

    rahu_trop = mean_node(jd)
    ketu_trop = norm360(rahu_trop + 180)
    moon_lat = moon_ecliptic_latitude(jd)
    sun_dec = declination(sun_trop, 0.0, jd)
    moon_dec = declination(moon_trop, moon_lat, jd)
    rahu_dec = declination(rahu_trop, 0.0, jd)
    ketu_dec = declination(ketu_trop, 0.0, jd)

    # ---- Special lagnas: Horā / Ghaṭikā / Bhāva / Vighaṭikā Lagna, from Iṣṭa Kāla
    # (time elapsed since sunrise, in ghatis) measured from the Sun's sidereal longitude.
    sunrise_ut = sunrise_utc_hours(y, mo, dd, lat, lon)
    sunrise_local = sunrise_ut + tz
    birth_local_hours = hh + mm / 60.0
    ishta_hours = birth_local_hours - sunrise_local
    if ishta_hours < 0:
        ishta_hours += 24.0
    ishta_ghatis = ishta_hours * 2.5

    ghatika_lagna_sid = norm360(sun_sid + ishta_ghatis * 30)
    hora_lagna_sid = norm360(sun_sid + ishta_ghatis * 15)
    bhava_lagna_sid = norm360(sun_sid + ishta_ghatis * 6)
    vighatika_lagna_sid = norm360(sun_sid + ishta_ghatis * 1800)

    # ---- Śrī Lagna: navamsa sign of the Ascendant, advanced by the Moon's navamsa count
    # within its own rāśi, with the Moon's fractional position inside that navamsa carried
    # over as the exact degree.
    navamsa_span = 30.0 / 9.0
    moon_sign_ = math.floor(moon_sid / 30)
    moon_in_sign_ = moon_sid - moon_sign_ * 30
    moon_nav_num = math.floor(moon_in_sign_ / navamsa_span)
    moon_nav_frac = (moon_in_sign_ - moon_nav_num * navamsa_span) / navamsa_span
    asc_d9_sign = navamsa_sign(asc_sid)
    sree_sign = int((asc_d9_sign + moon_nav_num) % 12)
    sree_lagna_sid = norm360(sree_sign * 30 + moon_nav_frac * 30)

    # ---- Prāṇapada Lagna: Sun's degree-in-sign × 5, counted from Sun's own sign
    # (movable), 9th from it (fixed), or 5th from it (dual).
    sun_sign_ = math.floor(sun_sid / 30)
    sun_in_sign_ = sun_sid - sun_sign_ * 30
    prana_deg = sun_in_sign_ * 5
    if sun_sign_ % 3 == 0:
        prana_start_sign = sun_sign_
    elif sun_sign_ % 3 == 1:
        prana_start_sign = (sun_sign_ + 8) % 12
    else:
        prana_start_sign = (sun_sign_ + 4) % 12
    pranapada_sid = norm360(prana_start_sign * 30 + prana_deg)

    raw_bodies = [
        ("As", "Lagna (Asc)", asc_sid, False, 0.0, 0.0),
        ("Su", "Sūrya (Sun)", sun_sid, False, 0.0, sun_dec),
        ("Mo", "Candra (Moon)", moon_sid, False, moon_lat, moon_dec),
        ("Ma", "Maṅgala (Mars)", planet_sid["Mars"], planet_retro["Mars"],
         planet_lat["Mars"], planet_dec["Mars"]),
        ("Me", "Budha (Mercury)", planet_sid["Mercury"], planet_retro["Mercury"],
         planet_lat["Mercury"], planet_dec["Mercury"]),
        ("Jp", "Guru (Jupiter)", planet_sid["Jupiter"], planet_retro["Jupiter"],
         planet_lat["Jupiter"], planet_dec["Jupiter"]),
        ("Ve", "Śukra (Venus)", planet_sid["Venus"], planet_retro["Venus"],
         planet_lat["Venus"], planet_dec["Venus"]),
        ("Sa", "Śani (Saturn)", planet_sid["Saturn"], planet_retro["Saturn"],
         planet_lat["Saturn"], planet_dec["Saturn"]),
        ("Ra", "Rāhu", rahu_sid, True, 0.0, rahu_dec),
        ("Ke", "Ketu", ketu_sid, True, 0.0, ketu_dec),
        ("HL", "Horā Lagna", hora_lagna_sid, False, 0.0, 0.0),
        ("BL", "Bhāva Lagna", bhava_lagna_sid, False, 0.0, 0.0),
        ("GL", "Ghaṭikā Lagna", ghatika_lagna_sid, False, 0.0, 0.0),
        ("ŚL", "Śrī Lagna", sree_lagna_sid, False, 0.0, 0.0),
        ("PP", "Prāṇapada Lagna", pranapada_sid, False, 0.0, 0.0),
        ("ViL", "Vighaṭikā Lagna", vighatika_lagna_sid, False, 0.0, 0.0),
    ]

    bodies = []
    for key, name, lon_, retro, lat_ecl, dec in raw_bodies:
        sign = math.floor(lon_ / 30)
        in_sign = lon_ - sign * 30
        nak_idx = math.floor(lon_ / (360 / 27))
        pada = math.floor((lon_ % (360 / 27)) / (360 / 108)) + 1
        bodies.append({
            "key": key, "name": name, "lon": lon_, "retro": retro,
            "sign": sign, "inSign": in_sign, "nakIdx": nak_idx, "pada": pada,
            "lat": lat_ecl, "dec": dec,
        })

    body_by_key = {b["key"]: b for b in bodies}
    karaka_degrees = {}
    for k in ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa"]:
        karaka_degrees[k] = body_by_key[k]["inSign"]
    karaka_degrees["Ra"] = 30.0 - body_by_key["Ra"]["inSign"]
    karaka_map = chara_karaka(karaka_degrees)
    for b in bodies:
        b["karaka"] = karaka_map.get(b["key"])

    combust_trop = {"Ma": planet_trop.get("Mars"), "Me": planet_trop.get("Mercury"),
                     "Jp": planet_trop.get("Jupiter"), "Ve": planet_trop.get("Venus"),
                     "Sa": planet_trop.get("Saturn")}
    for b in bodies:
        if b["key"] in combust_trop:
            diff = abs(norm360(combust_trop[b["key"]] - sun_trop))
            diff = min(diff, 360 - diff)
            b["combust"] = diff <= COMBUSTION_ORB[b["key"]]
        else:
            b["combust"] = False

    elong = norm360(moon_trop - sun_trop)
    tithi_idx = math.floor(elong / 12)
    tithi_pct = (elong % 12) / 12 * 100
    paksha = "Śukla" if tithi_idx < 15 else "Kṛṣṇa"
    if tithi_idx == 14:
        tithi_name = "Pūrṇimā"
    elif tithi_idx == 29:
        tithi_name = "Amāvasyā"
    else:
        tithi_name = TITHIS[tithi_idx % 15]

    nak_idx = math.floor(moon_sid / (360 / 27))
    nak_pct = (moon_sid % (360 / 27)) / (360 / 27) * 100
    nak_pada = math.floor((moon_sid % (360 / 27)) / (360 / 108)) + 1
    yoga_idx = math.floor(norm360(sun_sid + moon_sid) / (360 / 27))
    k_idx = math.floor(elong / 6)
    if k_idx == 0:
        karana = "Kiṁstughna"
    elif k_idx == 57:
        karana = "Śakuni"
    elif k_idx == 58:
        karana = "Catuṣpāda"
    elif k_idx == 59:
        karana = "Nāga"
    else:
        karana = KARANA_MOVABLE[(k_idx - 1) % 7]

    js_day = date(y, mo, dd).isoweekday() % 7
    vara = VARAS[js_day]

    nak_frac = (moon_sid % (360 / 27)) / (360 / 27)
    start_lord = nak_idx % 9
    balance_years = (1 - nak_frac) * DASHA_YEARS[start_lord]

    birth_dt_utc = datetime(y, mo, dd, hh, mm) - timedelta(hours=tz)
    YEAR_DAYS = 365.25
    dashas = []
    cursor = birth_dt_utc
    for i in range(9):
        lord_idx = (start_lord + i) % 9
        yrs = balance_years if i == 0 else DASHA_YEARS[lord_idx]
        end = cursor + timedelta(days=yrs * YEAR_DAYS)
        dashas.append({"lord": DASHA_LORDS[lord_idx], "lordIdx": lord_idx, "from": cursor, "to": end, "yrs": yrs})
        cursor = end

    return {
        "jd": jd,
        "ayanDate": ayan_date,
        "bodies": bodies,
        "ascSid": asc_sid,
        "panchanga": {
            "vara": vara, "paksha": paksha, "tithiName": tithi_name, "tithiIdx": tithi_idx,
            "tithiPct": tithi_pct, "nakIdx": nak_idx, "nakPct": nak_pct, "nakPada": nak_pada,
            "yogaIdx": yoga_idx, "karana": karana, "elong": elong,
        },
        "dashas": dashas,
    }


def compute_antardashas(maha_lord_idx: int, maha_start: datetime, maha_years: float):
    YEAR_DAYS = 365.25
    subs = []
    cursor = maha_start
    for i in range(9):
        lord_idx = (maha_lord_idx + i) % 9
        yrs = maha_years * DASHA_YEARS[lord_idx] / 120
        end = cursor + timedelta(days=yrs * YEAR_DAYS)
        subs.append({"lord": DASHA_LORDS[lord_idx], "lordIdx": lord_idx, "from": cursor, "to": end, "yrs": yrs})
        cursor = end
    return subs


def compute_pratyantardashas(antar_lord_idx: int, antar_start: datetime, antar_years: float):
    YEAR_DAYS = 365.25
    subs = []
    cursor = antar_start
    for i in range(9):
        lord_idx = (antar_lord_idx + i) % 9
        yrs = antar_years * DASHA_YEARS[lord_idx] / 120
        end = cursor + timedelta(days=yrs * YEAR_DAYS)
        subs.append({"lord": DASHA_LORDS[lord_idx], "from": cursor, "to": end, "yrs": yrs})
        cursor = end
    return subs


def now_in_city(tz: float) -> datetime:
    return datetime.utcnow() + timedelta(hours=tz)


# ============================================================
# COLORS  (butterscotch-tinted background)
# ============================================================

C = {
    "bg": "#FFF9C4", "panel": "#FFFDE7", "panelSoft": "#FFF3B0", "line": "#F0DE94",
    "gold": "#B8842E", "ivory": "#3A2E1F", "muted": "#7A6F5C", "sindoor": "#C4462B",
    "moon": "#3A5B8C",
}

HOUSE_CENTERS = [
    (200, 100), (100, 50), (50, 100), (102, 200), (50, 300), (100, 350),
    (200, 297), (300, 350), (350, 300), (298, 200), (350, 100), (300, 50),
]


def build_svg_chart(birth_bodies, transit_bodies, asc_sign: int) -> str:
    by_house = [{"b": [], "t": []} for _ in range(12)]
    for x in birth_bodies:
        by_house[(x["sign"] - asc_sign + 12) % 12]["b"].append(x)
    for x in transit_bodies:
        if x["key"] == "As":
            continue
        by_house[(x["sign"] - asc_sign + 12) % 12]["t"].append(x)

    def label(x, kind, cx, y):
        fill = C["sindoor"] if kind == "t" else (C["moon"] if x["key"] == "As" else C["ivory"])
        sub_fill = C["sindoor"] if kind == "t" else C["muted"]
        retro_mark = "℞" if (x["retro"] and x["key"] not in ("Ra", "Ke")) else ""
        deg = math.floor(x["inSign"])
        return (
            f'<text x="{cx}" y="{y}" text-anchor="middle" font-size="14" font-weight="700" '
            f'fill="{fill}" font-family="Georgia, serif">{x["key"]}'
            f'<tspan font-size="10" fill="{sub_fill}" font-family="monospace">'
            f' {deg}°{retro_mark}</tspan></text>'
        )

    parts = [
        '<svg viewBox="0 0 400 400" width="720" height="720" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="cbg" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDE7" /><stop offset="100%" stop-color="#FFF3B0" />'
        '</radialGradient></defs>',
        f'<rect x="2" y="2" width="396" height="396" fill="url(#cbg)" stroke="{C["gold"]}" stroke-width="2" />',
        f'<line x1="2" y1="2" x2="398" y2="398" stroke="{C["gold"]}" stroke-width="1" opacity="0.85" />',
        f'<line x1="398" y1="2" x2="2" y2="398" stroke="{C["gold"]}" stroke-width="1" opacity="0.85" />',
        f'<polygon points="200,2 398,200 200,398 2,200" fill="none" stroke="{C["gold"]}" '
        f'stroke-width="1" opacity="0.85" />',
    ]

    for h, (cx, cy) in enumerate(HOUSE_CENTERS):
        sign_num = ((asc_sign + h) % 12) + 1
        b, t = by_house[h]["b"], by_house[h]["t"]
        n = len(b) + len(t)
        step = 14
        start_y = cy - ((n - 1) * step) / 2 + 4
        parts.append(
            f'<text x="{cx}" y="{start_y - step - 2}" text-anchor="middle" font-size="10" '
            f'fill="{C["muted"]}" font-family="monospace">{sign_num}</text>'
        )
        for i, x in enumerate(b):
            parts.append(label(x, "b", cx, start_y + i * step))
        for i, x in enumerate(t):
            parts.append(label(x, "t", cx, start_y + (len(b) + i) * step))

    parts.append("</svg>")
    return "".join(parts)


def _wheel_point(cx, cy, r, clockwise_deg):
    rad = clockwise_deg * D2R
    return cx + r * math.sin(rad), cy - r * math.cos(rad)


def build_circular_svg_chart(birth_bodies, transit_bodies, asc_sign: int, asc_deg_in_sign: float) -> str:
    cx, cy = 300, 300
    R_outer = 280
    R_nak_out, R_nak_in = 272, 232
    R_sign_out, R_sign_in = 232, 198
    R_house_num = 178
    R_body_ring_out, R_body_ring_in = 198, 60

    def sign_center_angle(sign_idx):
        return -(sign_idx * 30) % 360

    def nak_center_angle(nak_idx):
        return -(nak_idx * (360 / 27)) % 360

    parts = [
        f'<svg viewBox="0 0 {2*cx} {2*cy}" width="720" height="720" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="cwheel" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDE7" /><stop offset="100%" stop-color="#FFF3B0" />'
        '</radialGradient></defs>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_outer}" fill="url(#cwheel)" stroke="{C["gold"]}" stroke-width="2"/>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_nak_in}" fill="none" stroke="{C["line"]}" stroke-width="1"/>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_sign_in}" fill="none" stroke="{C["gold"]}" stroke-width="1.2"/>',
    ]

    nak_span = 360 / 27
    nak_half = nak_span / 2
    pada_step = nak_span / 4

    for n in range(27):
        boundary = (-(n * nak_span) + nak_half) % 360
        x1, y1 = _wheel_point(cx, cy, R_nak_in, boundary)
        x2, y2 = _wheel_point(cx, cy, R_nak_out, boundary)
        parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                      f'stroke="{C["line"]}" stroke-width="1"/>')
        lx, ly = _wheel_point(cx, cy, R_nak_out - 7, nak_center_angle(n))
        parts.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="8.5" fill="{C["muted"]}" font-family="monospace">{n+1} {NAK_ABBR[n]}</text>')

        # pada sub-ticks (3 internal dividers) + pada numbers (1-4) in the inner part of the ring
        center = nak_center_angle(n)
        for k in range(1, 4):
            p_ang = (center - nak_half + k * pada_step) % 360
            px1, py1 = _wheel_point(cx, cy, R_nak_in, p_ang)
            px2, py2 = _wheel_point(cx, cy, R_nak_in + 13, p_ang)
            parts.append(f'<line x1="{px1:.1f}" y1="{py1:.1f}" x2="{px2:.1f}" y2="{py2:.1f}" '
                          f'stroke="{C["line"]}" stroke-width="0.75"/>')
        for k in range(4):
            pc_ang = (center - nak_half + (k + 0.5) * pada_step) % 360
            plx, ply = _wheel_point(cx, cy, R_nak_in + 6, pc_ang)
            parts.append(f'<text x="{plx:.1f}" y="{ply:.1f}" text-anchor="middle" dominant-baseline="middle" '
                          f'font-size="6.5" fill="{C["muted"]}" font-family="monospace">{k+1}</text>')

    for s in range(12):
        boundary = (-(s * 30) + 15) % 360
        x1, y1 = _wheel_point(cx, cy, R_sign_in - 10, boundary)
        x2, y2 = _wheel_point(cx, cy, R_sign_out, boundary)
        parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                      f'stroke="{C["gold"]}" stroke-width="1"/>')
        lx, ly = _wheel_point(cx, cy, (R_sign_out + R_sign_in) / 2, sign_center_angle(s))
        parts.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="14" font-weight="700" fill="{C["gold"]}" '
                      f'font-family="Georgia, serif">{SIGN_ABBR[s]}</text>')

    for s in range(12):
        boundary = (-(s * 30) + 15) % 360
        x1, y1 = _wheel_point(cx, cy, 30, boundary)
        x2, y2 = _wheel_point(cx, cy, R_sign_in - 10, boundary)
        parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                      f'stroke="{C["muted"]}" stroke-width="1" stroke-dasharray="3,3" opacity="0.6"/>')
        house_num = ((s - asc_sign) % 12) + 1
        hx, hy = _wheel_point(cx, cy, R_house_num, sign_center_angle(s))
        parts.append(f'<text x="{hx:.1f}" y="{hy:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="11" fill="{C["muted"]}" font-family="monospace">{house_num}</text>')

    asc_angle = (-(asc_sign * 30 + asc_deg_in_sign) + 15) % 360
    ax1, ay1 = _wheel_point(cx, cy, R_sign_in - 25, asc_angle)
    ax2, ay2 = _wheel_point(cx, cy, R_sign_out, asc_angle)
    parts.append(f'<line x1="{ax1:.1f}" y1="{ay1:.1f}" x2="{ax2:.1f}" y2="{ay2:.1f}" '
                 f'stroke="{C["moon"]}" stroke-width="2.5"/>')
    tx, ty = _wheel_point(cx, cy, R_body_ring_out + 14, asc_angle)
    parts.append(f'<text x="{tx:.1f}" y="{ty:.1f}" text-anchor="middle" dominant-baseline="middle" '
                 f'font-size="13" font-weight="700" fill="{C["moon"]}" '
                 f'font-family="Georgia, serif">As</text>')

    def place_bodies(bodies, ring_r, color_fn):
        by_sign = {}
        for b in bodies:
            if b["key"] == "As":
                continue
            by_sign.setdefault(b["sign"], []).append(b)
        for s, blist in by_sign.items():
            n = len(blist)
            spread = 18
            base_angle = sign_center_angle(s)
            for i, b in enumerate(blist):
                off = (i - (n - 1) / 2) * spread
                px, py = _wheel_point(cx, cy, ring_r, base_angle + off)
                fill = color_fn(b)
                retro_mark = "℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
                deg = math.floor(b["inSign"])
                parts.append(
                    f'<text x="{px:.1f}" y="{py:.1f}" text-anchor="middle" dominant-baseline="middle" '
                    f'font-size="12" font-weight="700" fill="{fill}" font-family="Georgia, serif">{b["key"]}'
                    f'<tspan font-size="8" fill="{fill}" font-family="monospace"> {deg}°{retro_mark}</tspan></text>'
                )

    place_bodies(birth_bodies, R_body_ring_out - 30, lambda b: C["ivory"])
    place_bodies(transit_bodies, R_body_ring_in + 15, lambda b: C["sindoor"])

    parts.append(f'<circle cx="{cx}" cy="{cy}" r="30" fill="{C["panel"]}" stroke="{C["gold"]}" stroke-width="1.5"/>')
    parts.append(f'<text x="{cx}" y="{cy}" text-anchor="middle" dominant-baseline="middle" '
                 f'font-size="30" fill="{C["gold"]}">ॐ</text>')

    parts.append("</svg>")
    return "".join(parts)


# ============================================================
# AUTH / DATABASE  — accounts (username + password only), saved profiles
# ============================================================
#
# Storage: a local SQLite file next to this script. Fine for a single-instance
# deployment; if you scale to multiple app instances behind a load balancer,
# swap DB_PATH for a shared Postgres/MySQL connection string instead — the
# functions below are the only place that would need to change.
#
# No email is collected or required. Uniqueness is enforced on username only
# (case-insensitive), so "PushpinderS" and "pushpinders" are the same account
# and a second signup with either casing is rejected.

DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kundali_users.db")

USERNAME_RE = re.compile(r"^[A-Za-z0-9_]{3,20}$")


def get_conn():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    conn = get_conn()
    conn.execute("""
        CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL,
            username_lower TEXT UNIQUE NOT NULL,
            pw_hash TEXT NOT NULL,
            pw_salt TEXT NOT NULL,
            created_at REAL NOT NULL
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS profiles (
            user_id INTEGER PRIMARY KEY,
            name TEXT, dob TEXT, tob TEXT,
            city_name TEXT, city_region TEXT, lat REAL, lon REAL, tz REAL,
            updated_at REAL,
            FOREIGN KEY(user_id) REFERENCES users(id)
        )
    """)
    conn.commit()
    conn.close()


def hash_password(password: str, salt_hex: str = None):
    if salt_hex is None:
        salt_hex = secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), 200_000
    ).hex()
    return digest, salt_hex


def check_password(password: str, salt_hex: str, stored_hash: str) -> bool:
    digest, _ = hash_password(password, salt_hex)
    return hmac.compare_digest(digest, stored_hash)


def username_taken(username: str) -> bool:
    conn = get_conn()
    row = conn.execute(
        "SELECT 1 FROM users WHERE username_lower=?", (username.lower(),)
    ).fetchone()
    conn.close()
    return row is not None


def create_user(username: str, password: str):
    """Returns (ok, message)."""
    conn = get_conn()
    pw_hash, pw_salt = hash_password(password)
    try:
        conn.execute(
            "INSERT INTO users (username, username_lower, pw_hash, pw_salt, created_at) "
            "VALUES (?, ?, ?, ?, ?)",
            (username, username.lower(), pw_hash, pw_salt, time.time()),
        )
        conn.commit()
        return True, ""
    except sqlite3.IntegrityError:
        return False, "That username is already taken — pick another one."
    finally:
        conn.close()


def authenticate(username: str, password: str):
    """Returns (user_dict_or_None, message)."""
    conn = get_conn()
    row = conn.execute(
        "SELECT * FROM users WHERE username_lower=?", (username.lower(),)
    ).fetchone()
    conn.close()
    if row is None:
        return None, "No account with that username."
    if not check_password(password, row["pw_salt"], row["pw_hash"]):
        return None, "Incorrect password."
    return dict(row), ""


def load_profile(user_id: int):
    conn = get_conn()
    row = conn.execute("SELECT * FROM profiles WHERE user_id=?", (user_id,)).fetchone()
    conn.close()
    return dict(row) if row else None


def save_profile(user_id: int, name, dob_iso, tob_iso, city_name, city_region, lat, lon, tz):
    conn = get_conn()
    conn.execute(
        """
        INSERT INTO profiles (user_id, name, dob, tob, city_name, city_region, lat, lon, tz, updated_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            name=excluded.name, dob=excluded.dob, tob=excluded.tob,
            city_name=excluded.city_name, city_region=excluded.city_region,
            lat=excluded.lat, lon=excluded.lon, tz=excluded.tz, updated_at=excluded.updated_at
        """,
        (user_id, name, dob_iso, tob_iso, city_name, city_region, lat, lon, tz, time.time()),
    )
    conn.commit()
    conn.close()


init_db()


def render_auth_screen():
    """Full-page login / signup flow. Returns nothing — sets
    st.session_state['user'] and reruns once authenticated."""
    st.markdown(
        f'<h1 style="color:{C["gold"]}; font-family:Georgia, serif; letter-spacing:0.06em;">Kuṇḍalī</h1>'
        f'<p class="kmuted" style="margin-top:-10px; font-size:16px;">Sign in to save your birth details '
        f'and come back to them anytime.</p>',
        unsafe_allow_html=True,
    )

    tab_login, tab_signup = st.tabs(["Log in", "Sign up"])

    with tab_login:
        st.markdown('<div class="kcard" style="max-width:440px;">', unsafe_allow_html=True)
        identifier = st.text_input("Username", key="login_identifier")
        password = st.text_input("Password", type="password", key="login_password")
        if st.button("Log in", use_container_width=True):
            if not identifier or not password:
                st.error("Enter your username and password.")
            else:
                user, msg = authenticate(identifier.strip(), password)
                if user:
                    st.session_state["user"] = {"id": user["id"], "username": user["username"]}
                    st.rerun()
                else:
                    st.error(msg)
        st.markdown("</div>", unsafe_allow_html=True)

    with tab_signup:
        st.markdown('<div class="kcard" style="max-width:440px;">', unsafe_allow_html=True)
        su_username = st.text_input("Username (3-20 letters/numbers/underscore)", key="su_username")
        su_pw = st.text_input("Password (min 8 characters)", type="password", key="su_pw")
        su_pw2 = st.text_input("Confirm password", type="password", key="su_pw2")
        su_terms = st.checkbox("I agree to the Terms of Service and Privacy Policy", key="su_terms")
        if st.button("Create account", use_container_width=True):
            errors = []
            if not USERNAME_RE.match(su_username or ""):
                errors.append("Username must be 3-20 characters: letters, numbers, underscore only.")
            elif username_taken(su_username):
                errors.append("That username is already taken — pick another one.")
            if len(su_pw or "") < 8:
                errors.append("Password must be at least 8 characters.")
            if su_pw != su_pw2:
                errors.append("Passwords don't match.")
            if not su_terms:
                errors.append("You must agree to the Terms of Service and Privacy Policy.")
            if errors:
                for e in errors:
                    st.error(e)
            else:
                ok, msg = create_user(su_username.strip(), su_pw)
                if not ok:
                    st.error(msg)
                else:
                    st.success("Account created — you can log in now.")
        st.markdown("</div>", unsafe_allow_html=True)


# ============================================================
# STREAMLIT APP
# ============================================================

st.set_page_config(page_title="Kuṇḍalī", page_icon="✨", layout="wide")

st.markdown(
    f"""
    <style>
    .stApp {{ background-color: {C["bg"]}; color: {C["ivory"]}; font-size: 17px; }}
    .kcard {{
        background: {C["panel"]}; border: 1px solid {C["line"]};
        border-radius: 12px; padding: 20px; margin-bottom: 18px;
        box-shadow: 0 1px 4px rgba(58,46,31,0.06);
    }}
    .kcard h4 {{
        color: {C["gold"]}; letter-spacing: 0.10em; font-size: 17px;
        text-transform: uppercase; border-bottom: 2px solid {C["line"]};
        padding-bottom: 10px; margin-bottom: 14px; font-family: Georgia, serif;
        font-weight: 700;
    }}
    .krow {{
        display: flex; justify-content: space-between; padding: 9px 0;
        border-bottom: 1px solid {C["line"]}; font-size: 17px;
    }}
    .kmuted {{ color: {C["muted"]}; }}
    .ksindoor {{ color: {C["sindoor"]}; font-weight: 600; }}
    p, span, div, label {{ font-size: 17px; }}
    .stDataFrame, .stDataFrame * {{ font-size: 16px !important; }}
    h1 {{ font-size: 42px !important; }}
    .gtable {{ width: 100%; border-collapse: collapse; font-size: 16px; }}
    .gtable th {{
        text-align: left; color: {C["gold"]}; font-weight: 700;
        padding: 6px 10px; border-bottom: 2px solid {C["line"]}; white-space: nowrap;
    }}
    .gtable td {{ padding: 7px 10px; border-bottom: 1px solid {C["line"]}; white-space: nowrap; }}
    .gtable tr:nth-child(even) {{ background: {C["panelSoft"]}; }}
    .gtable .lord {{ color: {C["sindoor"]}; font-weight: 600; }}
    .gtable .body-key {{ font-weight: 700; color: {C["sindoor"]}; }}
    .gtable th.uh {{ text-decoration: underline; }}
    </style>
    """,
    unsafe_allow_html=True,
)

# ---- Auth gate: nothing below runs until the person is logged in ----------
if "user" not in st.session_state:
    render_auth_screen()
    st.stop()

topbar_l, topbar_r = st.columns([4, 1])
with topbar_l:
    st.markdown(
        f'<h1 style="color:{C["gold"]}; font-family:Georgia, serif; letter-spacing:0.06em;">Kuṇḍalī</h1>'
        f'<p class="kmuted" style="margin-top:-10px; font-size:18px;">Vedic birth-chart engine · Lahiri ayanamsa · Python build</p>',
        unsafe_allow_html=True,
    )
with topbar_r:
    st.markdown("<br>", unsafe_allow_html=True)
    st.markdown(f'<p class="kmuted" style="text-align:right;">Signed in as <b>{st.session_state["user"]["username"]}</b></p>', unsafe_allow_html=True)
    if st.button("Log out", use_container_width=True):
        del st.session_state["user"]
        st.session_state.pop("form", None)
        st.rerun()

# ---- Load this user's saved birth details, if any, as form defaults -------
saved_profile = load_profile(st.session_state["user"]["id"])

# ---- Birth details form -------------------------------------------------
st.markdown('<div class="kcard"><h4>Birth details</h4>', unsafe_allow_html=True)

use_manual_coords = st.checkbox(
    "Enter latitude / longitude manually (place not in the city list)", value=False
)

col1, col2, col3, col4, col5 = st.columns([1.2, 1.6, 1, 1, 0.8])

with col1:
    name = st.text_input("Name", value=(saved_profile["name"] if saved_profile else ""), placeholder="Name of chart")

if use_manual_coords:
    # ---- Manual coordinates path: user supplies place name, lat, lon, tz directly ----
    default_place = saved_profile["city_name"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else ""
    default_mlat = saved_profile["lat"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 30.21
    default_mlon = saved_profile["lon"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 74.95
    default_mtz = saved_profile["tz"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 5.5
    with col2:
        place_name = st.text_input("Place name (for display only)", value=default_place, placeholder="e.g. Custom Town")
        mcol1, mcol2, mcol3 = st.columns(3)
        with mcol1:
            manual_lat = st.number_input(
                "Latitude", min_value=-90.0, max_value=90.0, value=float(default_mlat), step=0.0001, format="%.4f"
            )
        with mcol2:
            manual_lon = st.number_input(
                "Longitude", min_value=-180.0, max_value=180.0, value=float(default_mlon), step=0.0001, format="%.4f"
            )
        with mcol3:
            manual_tz = st.number_input(
                "UTC offset (h)", min_value=-12.0, max_value=14.0, value=float(default_mtz), step=0.25, format="%.2f"
            )
        st.caption(
            f"{abs(manual_lat):.4f}°{'N' if manual_lat >= 0 else 'S'}, "
            f"{abs(manual_lon):.4f}°{'E' if manual_lon >= 0 else 'W'} · "
            f"UTC{'+' if manual_tz >= 0 else ''}{manual_tz}"
        )
    city = (place_name if place_name else "Custom location", "Manual entry", manual_lat, manual_lon, manual_tz)
else:
    default_city_query = saved_profile["city_name"] if (saved_profile and saved_profile.get("city_region") != "Manual entry") else "Bathinda"
    with col2:
        city_query = st.text_input("Birth place (city)", value=default_city_query)
        matches = [c for c in CITIES if city_query.lower() in (c[0] + " " + c[1]).lower()]
        if not matches:
            matches = CITIES[:8]
        city_labels = [f"{c[0]} · {c[1]}" for c in matches[:8]]
        chosen_label = st.selectbox("Match", city_labels, label_visibility="collapsed")
        city = matches[city_labels.index(chosen_label)]
        st.caption(
            f"{abs(city[2]):.2f}°{'N' if city[2] >= 0 else 'S'}, "
            f"{abs(city[3]):.2f}°{'E' if city[3] >= 0 else 'W'} · UTC{'+' if city[4] >= 0 else ''}{city[4]}"
        )

with col3:
    default_dob = date.fromisoformat(saved_profile["dob"]) if (saved_profile and saved_profile.get("dob")) else date(2026, 7, 16)
    dob = st.date_input(
        "Date of birth", value=default_dob,
        min_value=date(1900, 1, 1), max_value=date(2100, 12, 31),
    )

with col4:
    default_tob = dtime.fromisoformat(saved_profile["tob"]) if (saved_profile and saved_profile.get("tob")) else dtime(12, 16)
    tob = st.time_input("Time (24h, local)", value=default_tob)

with col5:
    st.markdown("<br>", unsafe_allow_html=True)
    cast = st.button("Cast chart", use_container_width=True)

st.markdown("</div>", unsafe_allow_html=True)

# Keep last-cast form in session_state so the chart persists across reruns
if "form" not in st.session_state or cast:
    st.session_state["form"] = {
        "name": name, "dob": dob, "tob": tob, "city": city,
    }
    if cast:
        save_profile(
            st.session_state["user"]["id"], name, dob.isoformat(), tob.isoformat(),
            city[0], city[1], city[2], city[3], city[4],
        )
form = st.session_state["form"]

# ---- Compute birth chart + live transit ----------------------------------
lat, lon, tz = form["city"][2], form["city"][3], form["city"][4]

birth_chart = compute_chart(
    form["dob"].year, form["dob"].month, form["dob"].day,
    form["tob"].hour, form["tob"].minute, lat, lon, tz,
)

refresh = st.button("🔄 Refresh transits (updates to current time)")
now_local = now_in_city(tz)
transit_chart = compute_chart(
    now_local.year, now_local.month, now_local.day,
    now_local.hour, now_local.minute, lat, lon, tz,
)
transit_label = now_local.strftime("%d-%m-%Y %H:%M")

b_asc = next(b for b in birth_chart["bodies"] if b["key"] == "As")
b_moon = next(b for b in birth_chart["bodies"] if b["key"] == "Mo")
tp = transit_chart["panchanga"]

now_utc = datetime.utcnow()
tdict = {t["key"]: t for t in transit_chart["bodies"]}
core_birth_bodies = [b for b in birth_chart["bodies"] if b["key"] in CORE_KEYS]
core_transit_bodies = [b for b in transit_chart["bodies"] if b["key"] in CORE_KEYS]

# ---- Row 1: Diamond chart + Circular chart, each with its own D1..D60 selector ----
c1, c2 = st.columns([1, 1])

with c1:
    st.markdown(
        '<div class="kcard"><h4 style="display:flex;justify-content:space-between;'
        'align-items:center;border-bottom:none;margin-bottom:6px;padding-bottom:0;">'
        '<span>North Indian</span></h4>',
        unsafe_allow_html=True,
    )
    diamond_varga = st.selectbox(
        "Chart", VARGA_OPTIONS, index=0, key="diamond_varga_select", label_visibility="collapsed"
    )
    st.markdown(
        f'<p class="kmuted" style="font-size:12px;margin:2px 0 10px 0;'
        f'border-bottom:2px solid {C["line"]};padding-bottom:8px;">{form["city"][0]}</p>',
        unsafe_allow_html=True,
    )
    dv_birth = make_varga_bodies(core_birth_bodies, diamond_varga)
    dv_transit = make_varga_bodies(core_transit_bodies, diamond_varga)
    dv_asc = next(b for b in dv_birth if b["key"] == "As")
    svg_diamond = build_svg_chart(dv_birth, dv_transit, dv_asc["sign"])
    st.components.v1.html(
        f'<div style="display:flex;justify-content:center;">{svg_diamond}</div>', height=760
    )
    st.markdown("</div>", unsafe_allow_html=True)

with c2:
    st.markdown(
        '<div class="kcard"><h4 style="display:flex;justify-content:space-between;'
        'align-items:center;border-bottom:none;margin-bottom:6px;padding-bottom:0;">'
        '<span>Rāśi Wheel</span></h4>',
        unsafe_allow_html=True,
    )
    circular_varga = st.selectbox(
        "Chart", VARGA_OPTIONS, index=0, key="circular_varga_select", label_visibility="collapsed"
    )
    st.markdown(
        f'<p class="kmuted" style="font-size:12px;margin:2px 0 10px 0;'
        f'border-bottom:2px solid {C["line"]};padding-bottom:8px;">transits {transit_label}</p>',
        unsafe_allow_html=True,
    )
    cv_birth = make_varga_bodies(core_birth_bodies, circular_varga)
    cv_transit = make_varga_bodies(core_transit_bodies, circular_varga)
    cv_asc = next(b for b in cv_birth if b["key"] == "As")
    svg_circular = build_circular_svg_chart(
        cv_birth, cv_transit, cv_asc["sign"], cv_asc["inSign"]
    )
    st.components.v1.html(
        f'<div style="display:flex;justify-content:center;">{svg_circular}</div>', height=760
    )
    st.markdown("</div>", unsafe_allow_html=True)

# ---- Row 2: Nakṣatra table + Vimśottarī Mahādaśā + Pañcāṅga -------------
c4, c5, c6 = st.columns([1, 1, 0.8])

with c4:
    st.markdown('<div class="kcard"><h4>Nakṣatra · birth</h4>', unsafe_allow_html=True)
    nak_rows = "".join(
        f'<div class="krow"><span class="kmuted body-key">{b["key"]}</span>'
        f'<span style="text-align:right;">{NAKSHATRAS[b["nakIdx"]]}'
        f'<span class="kmuted">({b["nakIdx"]+1})</span> '
        f'<span class="lord ksindoor">{DASHA_LORD_SHORT[b["nakIdx"] % 9]}</span>'
        f'<br><span class="kmuted" style="font-size:13px;">pada {b["pada"]}</span></span></div>'
        for b in core_birth_bodies
    )
    st.markdown(nak_rows + "</div>", unsafe_allow_html=True)

with c5:
    moon_nak_idx = birth_chart["panchanga"]["nakIdx"]
    st.markdown(
        f'<div class="kcard"><h4>Viṁśottarī Daśā</h4>'
        f'<p class="kmuted" style="margin-bottom:10px;">Starting Tārā '
        f'<span class="ksindoor">Mo</span> ({NAKSHATRAS[moon_nak_idx]})</p>',
        unsafe_allow_html=True,
    )
    for d in birth_chart["dashas"]:
        active_maha = d["from"] <= now_utc < d["to"]
        marker = "🔶 " if active_maha else "▫️ "
        label = f'{marker}{d["lord"]}   {d["from"].strftime("%Y-%m-%d")} to {d["to"].strftime("%Y-%m-%d")}   ({d["yrs"]:.1f}y)'
        with st.expander(label, expanded=False):
            antardashas = compute_antardashas(d["lordIdx"], d["from"], d["yrs"])
            for i, a in enumerate(antardashas):
                active_a = a["from"] <= now_utc < a["to"]
                style = (
                    f"background:{C['panelSoft']};border:1px solid {C['gold']};"
                    if active_a else "border:1px solid transparent;"
                )
                color = C["gold"] if active_a else C["ivory"]
                st.markdown(
                    f'<div style="{style}border-radius:6px;padding:6px 10px;margin-bottom:4px;'
                    f'display:flex;justify-content:space-between;align-items:center;font-size:14px;">'
                    f'<span style="color:{color};font-weight:600;min-width:90px;">{a["lord"]}</span>'
                    f'<span class="kmuted" style="font-family:monospace;font-size:12px;flex:1;text-align:center;">'
                    f'{a["from"].strftime("%d %b %Y")} → {a["to"].strftime("%d %b %Y")}</span>'
                    f'<span class="kmuted" style="font-size:12px;">{a["yrs"]*12:.1f}mo</span>'
                    f'</div>',
                    unsafe_allow_html=True,
                )
                pratyantardashas = compute_pratyantardashas(a["lordIdx"], a["from"], a["yrs"])
                praty_rows = []
                for p in pratyantardashas:
                    active_p = p["from"] <= now_utc < p["to"]
                    p_style = (
                        f"background:{C['bg']};border-left:3px solid {C['sindoor']};"
                        if active_p else "border-left:3px solid transparent;"
                    )
                    p_color = C["sindoor"] if active_p else C["muted"]
                    praty_rows.append(
                        f'<div style="{p_style}border-radius:4px;padding:3px 8px 3px 14px;'
                        f'margin-left:18px;margin-bottom:2px;display:flex;justify-content:space-between;'
                        f'align-items:center;font-size:12px;">'
                        f'<span style="color:{p_color};font-weight:600;min-width:80px;">{p["lord"]}</span>'
                        f'<span class="kmuted" style="font-family:monospace;font-size:11px;flex:1;text-align:center;">'
                        f'{p["from"].strftime("%d %b %Y")} → {p["to"].strftime("%d %b %Y")}</span>'
                        f'<span class="kmuted" style="font-size:11px;">{p["yrs"]*365.25:.0f}d</span>'
                        f'</div>'
                    )
                st.markdown("".join(praty_rows), unsafe_allow_html=True)
    st.markdown(
        '<p class="kmuted" style="font-size:13px;margin-top:10px;">'
        "🔶 = currently running mahādaśā. Click any row to see its antardaśā (sub-periods), "
        "with pratyantardaśā (sub-sub-periods) listed underneath each.</p></div>",
        unsafe_allow_html=True,
    )

with c6:
    st.markdown('<div class="kcard"><h4>Pañcāṅga · at birth</h4>', unsafe_allow_html=True)
    rows = [
        ("Vāra", birth_chart["panchanga"]["vara"]),
        ("Tithi", f"{birth_chart['panchanga']['paksha']} {birth_chart['panchanga']['tithiName']} "
                  f"· {birth_chart['panchanga']['tithiPct']:.1f}%"),
        ("Nakṣatra", f"{NAKSHATRAS[birth_chart['panchanga']['nakIdx']]} · pada "
                      f"{birth_chart['panchanga']['nakPada']}"),
        ("Yoga", YOGAS[birth_chart["panchanga"]["yogaIdx"]]),
        ("Karaṇa", birth_chart["panchanga"]["karana"]),
        ("Ayanāṁśa", f"{fmt_deg(birth_chart['ayanDate'])} (Lahiri)"),
        ("Lagna", f"{SIGNS[b_asc['sign']]} {fmt_deg(b_asc['inSign'])}"),
        ("Moon sign", SIGNS[b_moon["sign"]]),
    ]
    rows_html = "".join(
        f'<div class="krow"><span class="kmuted">{k}</span><span>{v}</span></div>' for k, v in rows
    )
    st.markdown(
        f'{rows_html}'
        f'<p class="ksindoor" style="font-size:14px;margin-top:10px;">'
        f'Now: {tp["paksha"]} {tp["tithiName"]} · {NAKSHATRAS[tp["nakIdx"]]}</p></div>',
        unsafe_allow_html=True,
    )
    st.markdown(
        f"""
        <div style="display:flex;gap:14px;flex-wrap:wrap;font-size:13px;">
            <span><span style="color:{C['ivory']}">●</span> Birth</span>
            <span class="ksindoor"><span style="color:{C['sindoor']}">●</span> Transit · now</span>
            <span class="kmuted">℞ retrograde</span>
        </div>
        """,
        unsafe_allow_html=True,
    )

# ---- Row 3: Graha Info table (full width, includes special lagnas) --------
st.markdown('<div class="kcard"><h4>Graha Info</h4>', unsafe_allow_html=True)

header = (
    '<tr><th class="uh">Body</th><th class="uh">Kāraka</th><th>Long</th><th>Lat</th>'
    '<th>Dec</th><th class="uh">Nakṣatra</th><th>Pada</th></tr>'
)
body_rows = []
for b in birth_chart["bodies"]:
    retro_mark = " ℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
    combust_mark = " 🔥" if b.get("combust") else ""
    # the two senior Chara Kārakas (Ātmakāraka, Amātyakāraka) get the ↑ marker
    top_karaka_mark = '<span class="kmuted" style="font-size:11px;">↑</span> ' if b.get("karaka") in ("AK", "AmK") else ""
    long_str = f'{SIGN_ABBR[b["sign"]]} {fmt_dms(b["inSign"])}'
    nak_lord = DASHA_LORD_SHORT[b["nakIdx"] % 9]
    nak_str = f'{NAKSHATRAS[b["nakIdx"]]}<span class="kmuted">({b["nakIdx"]+1})</span> <span class="lord">{nak_lord}</span>'
    body_rows.append(
        f'<tr><td><span class="body-key">{b["key"]}</span>&nbsp;'
        f'{top_karaka_mark}{b["name"]}{retro_mark}{combust_mark}</td>'
        f'<td class="kmuted">{b["karaka"] or ""}</td>'
        f'<td style="font-family:monospace;">{long_str}</td>'
        f'<td class="kmuted" style="font-family:monospace;">{fmt_dms(b["lat"])}</td>'
        f'<td class="kmuted" style="font-family:monospace;">{fmt_dms(b["dec"])}</td>'
        f'<td>{nak_str}</td>'
        f'<td>{b["pada"]}</td></tr>'
    )

st.markdown(
    f'<div style="overflow-x:auto;"><table class="gtable">{header}{"".join(body_rows)}</table></div>'
    f'<p class="kmuted" style="font-size:13px;margin-top:10px;">'
    "Kāraka = classical 8-graha Chara Kāraka (AK=Ātmakāraka … DK=Dārakāraka), ↑ marks AK & AmK. "
    "HL/BL/GL/ŚL/PP/ViL are the special lagnas (Horā, Bhāva, Ghaṭikā, Śrī, Prāṇapada, Vighaṭikā), "
    "computed from Iṣṭa Kāla — standard formulas, worth cross-checking against a trusted source. "
    "🔥 = combust. ℞ = retrograde.</p></div>",
    unsafe_allow_html=True,
)

st.markdown(
    '<p class="kmuted" style="font-size:12px;">Engine accuracy: Sun/Moon a few arc-minutes, '
    "planets ~0.1–0.5°, mean Rāhu. For production, use Swiss Ephemeris + a geocoding API.</p>",
    unsafe_allow_html=True,
)

st.caption("Tip: click **🔄 Refresh transits** any time to update the red transit positions to right now.")
