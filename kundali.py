"""
KUNDALI — Vedic birth-chart engine (Python / Streamlit port)
-------------------------------------------------------------
- City-name lookup (built-in gazetteer)
- Combined chart: birth (ivory) + live transits (red)
- Houses fixed to the birth lagna, degrees on every graha

Run with:
    pip install streamlit pandas requests fpdf2
    streamlit run kundali_app.py

Razorpay setup (required for real payments):
    1. Sign up at https://dashboard.razorpay.com/signup
    2. Complete KYC to go live, or just use Test Mode to develop first
       (Settings -> API Keys -> Generate Test Key)
    3. Set these as environment variables (on Render: Dashboard -> your
       service -> Environment):
         RAZORPAY_KEY_ID=rzp_test_xxxxxxxx   (or rzp_live_... once verified)
         RAZORPAY_KEY_SECRET=xxxxxxxxxxxxxxxx
    4. Also set your Streamlit app's public URL so the checkout redirect
       comes back to the right place:
         APP_BASE_URL=https://yourdomain.com
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
import requests

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

def compute_chart(y: int, mo: int, dd: int, hh: int, mm: int, lat: float, lon: float, tz: float, ss: int = 0) -> dict:
    ut_hours = hh + mm / 60 + ss / 3600 - tz
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
    birth_local_hours = hh + mm / 60.0 + ss / 3600.0
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

    birth_dt_utc = datetime(y, mo, dd, hh, mm, ss) - timedelta(hours=tz)
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

DB_PATH = os.path.join(os.environ.get("DB_DIR", os.path.dirname(os.path.abspath(__file__))), "kundali_users.db")

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

    # ---- Migration: an older deployment may have created "users" before the
    # email-verification columns were removed. CREATE TABLE IF NOT EXISTS
    # above is a no-op on an existing table, so detect and fix it here
    # instead of crashing on a missing column / stale NOT NULL constraint.
    cols_info = conn.execute("PRAGMA table_info(users)").fetchall()
    existing_cols = {row["name"] for row in cols_info}
    has_old_columns = "email" in existing_cols or "verified" in existing_cols
    missing_username_lower = "username_lower" not in existing_cols

    if has_old_columns:
        # Old schema had NOT NULL columns (e.g. email) we no longer populate,
        # so patch that table won't work — rebuild it from scratch, keeping
        # id/username/pw_hash/pw_salt/created_at from whatever accounts exist.
        conn.execute("ALTER TABLE users RENAME TO users_old")
        conn.execute("""
            CREATE TABLE users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL,
                username_lower TEXT UNIQUE NOT NULL,
                pw_hash TEXT NOT NULL,
                pw_salt TEXT NOT NULL,
                created_at REAL NOT NULL
            )
        """)
        old_rows = conn.execute("SELECT * FROM users_old ORDER BY id").fetchall()
        seen_lower = set()
        for r in old_rows:
            uname = r["username"]
            uname_lower = uname.lower()
            if uname_lower in seen_lower:
                continue  # skip case-collision duplicates, keep the earliest account
            seen_lower.add(uname_lower)
            conn.execute(
                "INSERT INTO users (id, username, username_lower, pw_hash, pw_salt, created_at) "
                "VALUES (?, ?, ?, ?, ?, ?)",
                (r["id"], uname, uname_lower, r["pw_hash"], r["pw_salt"], r["created_at"]),
            )
        conn.execute("DROP TABLE users_old")
    elif missing_username_lower:
        conn.execute("ALTER TABLE users ADD COLUMN username_lower TEXT")
        conn.execute("UPDATE users SET username_lower = lower(username) WHERE username_lower IS NULL")
        dupes = conn.execute("""
            SELECT username_lower FROM users
            WHERE username_lower IS NOT NULL
            GROUP BY username_lower HAVING COUNT(*) > 1
        """).fetchall()
        for row in dupes:
            ids = [r["id"] for r in conn.execute(
                "SELECT id FROM users WHERE username_lower=? ORDER BY id", (row["username_lower"],)
            ).fetchall()]
            for extra_id in ids[1:]:
                conn.execute("DELETE FROM users WHERE id=?", (extra_id,))
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_users_username_lower ON users(username_lower)")

    # ---- Migration: add is_premium if this DB predates the premium feature.
    cols_now = {row["name"] for row in conn.execute("PRAGMA table_info(users)").fetchall()}
    if "is_premium" not in cols_now:
        conn.execute("ALTER TABLE users ADD COLUMN is_premium INTEGER NOT NULL DEFAULT 0")

    # ---- Real-money payments ledger. razorpay_payment_id is UNIQUE so a
    # payment can only ever be applied once, even if the success redirect
    # somehow fires twice (double click, page refresh, browser back button).
    conn.execute("""
        CREATE TABLE IF NOT EXISTS payments (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            razorpay_order_id TEXT NOT NULL,
            razorpay_payment_id TEXT UNIQUE,
            amount_paise INTEGER NOT NULL,
            status TEXT NOT NULL DEFAULT 'created',
            created_at REAL NOT NULL,
            verified_at REAL,
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


def is_premium(user_id: int) -> bool:
    conn = get_conn()
    row = conn.execute("SELECT is_premium FROM users WHERE id=?", (user_id,)).fetchone()
    conn.close()
    return bool(row and row["is_premium"])


def set_premium(user_id: int, value: bool = True):
    conn = get_conn()
    conn.execute("UPDATE users SET is_premium=? WHERE id=?", (1 if value else 0, user_id))
    conn.commit()
    conn.close()


def record_order(user_id: int, order_id: str, amount_paise: int):
    conn = get_conn()
    conn.execute(
        "INSERT INTO payments (user_id, razorpay_order_id, amount_paise, status, created_at) "
        "VALUES (?, ?, ?, 'created', ?)",
        (user_id, order_id, amount_paise, time.time()),
    )
    conn.commit()
    conn.close()


def payment_already_verified(payment_id: str) -> bool:
    conn = get_conn()
    row = conn.execute(
        "SELECT 1 FROM payments WHERE razorpay_payment_id=? AND status='paid'", (payment_id,)
    ).fetchone()
    conn.close()
    return row is not None


def mark_order_paid(order_id: str, payment_id: str) -> bool:
    """Attach the payment id to its order and flip it to paid. Returns False if this
    order was already marked paid or the payment id was already used elsewhere
    (both cases mean: don't grant premium again)."""
    conn = get_conn()
    row = conn.execute(
        "SELECT id, user_id, status FROM payments WHERE razorpay_order_id=?", (order_id,)
    ).fetchone()
    if row is None or row["status"] == "paid":
        conn.close()
        return False
    try:
        conn.execute(
            "UPDATE payments SET razorpay_payment_id=?, status='paid', verified_at=? WHERE id=?",
            (payment_id, time.time(), row["id"]),
        )
        conn.commit()
        return True
    except sqlite3.IntegrityError:
        # payment_id already attached to a different order — replay attempt
        conn.close()
        return False
    finally:
        conn.close()


def order_owner(order_id: str):
    conn = get_conn()
    row = conn.execute("SELECT user_id, amount_paise FROM payments WHERE razorpay_order_id=?", (order_id,)).fetchone()
    conn.close()
    return dict(row) if row else None


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
# PREMIUM: Kundali report generation (PDF, with HTML fallback)
# ============================================================

try:
    from fpdf import FPDF
    HAS_FPDF = True
except ImportError:
    HAS_FPDF = False

# ---- ASCII-safe transliterations for the PDF ------------------------------
# fpdf2's built-in core fonts (Helvetica etc.) only support Latin-1/WinAnsi,
# so IAST diacritics (ā, ṛ, ś, ṇ ...) used elsewhere in the app would either
# raise an encode error or render as garbage. Rather than bundle a Unicode
# TTF font, the PDF report uses these plain-ASCII equivalents throughout.

SIGNS_ASCII = ["Aries", "Taurus", "Gemini", "Cancer", "Leo", "Virgo", "Libra", "Scorpio",
               "Sagittarius", "Capricorn", "Aquarius", "Pisces"]

NAKSHATRAS_ASCII = [
    "Ashwini", "Bharani", "Krittika", "Rohini", "Mrigashira", "Ardra", "Punarvasu",
    "Pushya", "Ashlesha", "Magha", "Purva Phalguni", "Uttara Phalguni", "Hasta",
    "Chitra", "Swati", "Vishakha", "Anuradha", "Jyeshtha", "Mula", "Purva Ashadha",
    "Uttara Ashadha", "Shravana", "Dhanishtha", "Shatabhisha", "Purva Bhadrapada",
    "Uttara Bhadrapada", "Revati",
]

NAK_ABBR_ASCII = ["Aswi", "Bhar", "Krit", "Rohi", "Mrig", "Ardr", "Puna", "Push", "Asle",
                  "Magh", "PPha", "UPha", "Hast", "Chit", "Swat", "Visa", "Anur", "Jyes",
                  "Mula", "PAsh", "UAsh", "Shra", "Dhan", "Shat", "PBha", "UBha", "Reva"]

TITHIS_ASCII = ["Pratipada", "Dvitiya", "Tritiya", "Chaturthi", "Panchami", "Shashthi",
                "Saptami", "Ashtami", "Navami", "Dashami", "Ekadashi", "Dwadashi",
                "Trayodashi", "Chaturdashi"]

YOGAS_ASCII = ["Vishkambha", "Priti", "Ayushman", "Saubhagya", "Shobhana", "Atiganda",
               "Sukarma", "Dhriti", "Shula", "Ganda", "Vriddhi", "Dhruva", "Vyaghata",
               "Harshana", "Vajra", "Siddhi", "Vyatipata", "Variyan", "Parigha", "Shiva",
               "Siddha", "Sadhya", "Shubha", "Shukla", "Brahma", "Indra", "Vaidhriti"]

KARANA_ASCII_MAP = {
    "Kiṁstughna": "Kimstughna", "Bava": "Bava", "Bālava": "Balava", "Kaulava": "Kaulava",
    "Taitila": "Taitila", "Gara": "Gara", "Vaṇija": "Vanija", "Viṣṭi": "Vishti",
    "Śakuni": "Shakuni", "Catuṣpāda": "Chatushpada", "Nāga": "Naga",
}

DASHA_LORDS_ASCII = ["Ketu", "Venus", "Sun", "Moon", "Mars", "Rahu", "Jupiter", "Saturn", "Mercury"]

BODY_FULLNAME_ASCII = {
    "As": "Ascendant (Lagna)", "Su": "Sun", "Mo": "Moon", "Ma": "Mars", "Me": "Mercury",
    "Jp": "Jupiter", "Ve": "Venus", "Sa": "Saturn", "Ra": "Rahu", "Ke": "Ketu",
    "HL": "Hora Lagna", "BL": "Bhava Lagna", "GL": "Ghatika Lagna",
    "\u015aL": "Sri Lagna", "PP": "Pranapada Lagna", "ViL": "Vighatika Lagna",
}


def _fmt_deg_ascii(x: float) -> str:
    """Same as fmt_deg but uses a plain apostrophe instead of the prime (′)
    symbol, which isn't in Latin-1 and would break fpdf2's core fonts."""
    d = math.floor(x)
    m = math.floor((x - d) * 60)
    return f"{d}\u00b0{m:02d}'"


def _ascii_key(key: str) -> str:
    return "SL" if key == "\u015aL" else key


def _tithi_ascii(pan: dict) -> tuple:
    idx = pan["tithiIdx"]
    paksha = "Shukla" if idx < 15 else "Krishna"
    if idx == 14:
        name = "Purnima"
    elif idx == 29:
        name = "Amavasya"
    else:
        name = TITHIS_ASCII[idx % 15]
    return paksha, name


# Fractional (x, y) center of each house within the diamond chart's bounding
# square, in the same North-Indian layout as the on-screen SVG chart.
HOUSE_FRACS = [
    (0.5, 0.25), (0.25, 0.125), (0.125, 0.25), (0.255, 0.5),
    (0.125, 0.75), (0.25, 0.875), (0.5, 0.7425), (0.75, 0.875),
    (0.875, 0.75), (0.745, 0.5), (0.875, 0.25), (0.75, 0.125),
]


def draw_diamond_chart_pdf(pdf, bodies, asc_sign: int, asc_body: dict, x0: float, y0: float, size: float):
    """Draws a real North-Indian diamond Rasi chart directly with fpdf2's vector
    primitives (no external image/rasterizer needed)."""
    x1, y1 = x0 + size, y0 + size
    midx, midy = x0 + size / 2, y0 + size / 2

    pdf.set_draw_color(184, 132, 46)
    pdf.set_line_width(0.5)
    pdf.rect(x0, y0, size, size)
    pdf.line(x0, y0, x1, y1)
    pdf.line(x1, y0, x0, y1)
    pdf.set_line_width(0.35)
    pdf.line(midx, y0, x1, midy)
    pdf.line(x1, midy, midx, y1)
    pdf.line(midx, y1, x0, midy)
    pdf.line(x0, midy, midx, y0)

    by_house = [[] for _ in range(12)]
    for b in bodies:
        if b["key"] == "As":
            continue
        by_house[(b["sign"] - asc_sign + 12) % 12].append(b)

    for h, (fx, fy) in enumerate(HOUSE_FRACS):
        cx, cy = x0 + fx * size, y0 + fy * size
        sign_num = ((asc_sign + h) % 12) + 1
        lines = []
        if h == 0:
            lines.append(f'As {int(asc_body["inSign"])}\u00b0')
        for b in by_house[h]:
            deg = int(b["inSign"])
            retro = "R" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
            lines.append(f'{_ascii_key(b["key"])} {deg}\u00b0{retro}')

        block_h = len(lines) * 4.2
        pdf.set_font("Helvetica", "", 7)
        pdf.set_text_color(122, 111, 92)
        pdf.text(cx - 3, cy - block_h / 2 - 3, str(sign_num))

        ty = cy - block_h / 2
        for line in lines:
            pdf.set_font("Helvetica", "B", 8)
            pdf.set_text_color(196, 70, 43) if (line.startswith("As ")) else pdf.set_text_color(58, 46, 31)
            pdf.set_xy(cx - 16, ty)
            pdf.cell(32, 4.2, line, align="C")
            ty += 4.2


def generate_kundali_pdf_bytes(birth_chart, form) -> bytes:
    GOLD, IVORY, SINDOOR, MUTED = (184, 132, 46), (58, 46, 31), (196, 70, 43), (122, 111, 92)
    LINE, PANEL_SOFT, WHITE = (222, 196, 120), (255, 243, 176), (255, 253, 231)

    b_asc = next(b for b in birth_chart["bodies"] if b["key"] == "As")
    b_moon = next(b for b in birth_chart["bodies"] if b["key"] == "Mo")
    pan = birth_chart["panchanga"]
    core_bodies = [b for b in birth_chart["bodies"] if b["key"] in CORE_KEYS]
    paksha_ascii, tithi_ascii = _tithi_ascii(pan)
    karana_ascii = KARANA_ASCII_MAP.get(pan["karana"], pan["karana"])

    pdf = FPDF(format="A4", unit="mm")
    pdf.set_auto_page_break(auto=True, margin=18)
    pdf.set_margins(15, 15, 15)
    pdf.set_title("Kundali Report")

    def banner(title, subtitle=""):
        pdf.set_fill_color(*GOLD)
        pdf.rect(0, 0, 210, 26, "F")
        pdf.set_xy(0, 6)
        pdf.set_text_color(*WHITE)
        pdf.set_font("Helvetica", "B", 20)
        pdf.cell(210, 10, title, align="C")
        if subtitle:
            pdf.set_xy(0, 17)
            pdf.set_font("Helvetica", "", 10)
            pdf.cell(210, 6, subtitle, align="C")
        pdf.set_y(32)
        pdf.set_text_color(*IVORY)

    def section(text):
        pdf.ln(3)
        pdf.set_font("Helvetica", "B", 12)
        pdf.set_text_color(*GOLD)
        pdf.cell(0, 8, text, ln=True)
        y = pdf.get_y()
        pdf.set_draw_color(*LINE)
        pdf.set_line_width(0.4)
        pdf.line(15, y, 195, y)
        pdf.ln(2)
        pdf.set_text_color(*IVORY)

    def kv_row(k, v):
        pdf.set_font("Helvetica", "", 10)
        pdf.set_text_color(*MUTED)
        pdf.cell(55, 6.5, k)
        pdf.set_font("Helvetica", "B", 10)
        pdf.set_text_color(*IVORY)
        pdf.cell(0, 6.5, str(v), ln=True)

    def table(headers, rows, widths, row_h=6.5):
        pdf.set_font("Helvetica", "B", 9)
        pdf.set_fill_color(*GOLD)
        pdf.set_text_color(*WHITE)
        for h, w in zip(headers, widths):
            pdf.cell(w, 7, h, border=0, fill=True, align="C")
        pdf.ln(7)
        pdf.set_font("Helvetica", "", 8.5)
        for i, row in enumerate(rows):
            if pdf.get_y() + row_h > 279:
                pdf.add_page()
                pdf.set_font("Helvetica", "B", 9)
                pdf.set_fill_color(*GOLD)
                pdf.set_text_color(*WHITE)
                for h, w in zip(headers, widths):
                    pdf.cell(w, 7, h, border=0, fill=True, align="C")
                pdf.ln(7)
                pdf.set_font("Helvetica", "", 8.5)
            pdf.set_fill_color(*(PANEL_SOFT if i % 2 == 0 else WHITE))
            pdf.set_text_color(*IVORY)
            for cell_val, w in zip(row, widths):
                pdf.cell(w, row_h, str(cell_val), border=0, fill=True, align="C")
            pdf.ln(row_h)

    # ---------------- Page 1: cover, birth details, Rasi chart ----------------
    pdf.add_page()
    banner("KUNDALI", "Vedic Birth Chart Report")
    section("Birth Details")
    kv_row("Name", form["name"] or "-")
    kv_row("Date of Birth", form["dob"].strftime("%d %B %Y"))
    kv_row("Time of Birth", form["tob"].strftime("%H:%M:%S"))
    kv_row("Place of Birth", f'{form["city"][0]}, {form["city"][1]}')
    kv_row("Ayanamsa", f"{_fmt_deg_ascii(birth_chart['ayanDate'])} (Lahiri)")
    kv_row("Lagna (Ascendant)", f"{SIGNS_ASCII[b_asc['sign']]}  {_fmt_deg_ascii(b_asc['inSign'])}")
    kv_row("Moon Sign (Rasi)", SIGNS_ASCII[b_moon["sign"]])
    kv_row("Birth Nakshatra", f"{NAKSHATRAS_ASCII[pan['nakIdx']]}  -  Pada {pan['nakPada']}")

    section("Rasi Chart (D1) - North Indian Style")
    chart_size = 130
    x0 = (210 - chart_size) / 2
    y0 = pdf.get_y() + 2
    draw_diamond_chart_pdf(pdf, core_bodies, b_asc["sign"], b_asc, x0, y0, chart_size)
    pdf.set_y(y0 + chart_size + 5)
    pdf.set_font("Helvetica", "I", 8)
    pdf.set_text_color(*MUTED)
    pdf.cell(0, 5, "Houses are fixed to the birth lagna. R = retrograde.", ln=True, align="C")

    # ---------------- Page 2: Panchanga + Chara Karaka ----------------
    pdf.add_page()
    banner("PANCHANGA", "Five Limbs of the Almanac, at the Moment of Birth")
    section("Panchanga at Birth")
    kv_row("Vara (Weekday)", form["dob"].strftime("%A"))
    kv_row("Tithi (Lunar Day)", f"{paksha_ascii} Paksha, {tithi_ascii}  ({pan['tithiPct']:.1f}% elapsed)")
    kv_row("Nakshatra", f"{NAKSHATRAS_ASCII[pan['nakIdx']]}  -  Pada {pan['nakPada']}")
    kv_row("Yoga", YOGAS_ASCII[pan["yogaIdx"]])
    kv_row("Karana", karana_ascii)

    section("Chara Karaka (Significators)")
    karaka_rows = []
    karaka_order = ["AK", "AmK", "BK", "MK", "PiK", "PK", "GK", "DK"]
    karaka_names = {
        "AK": "Atmakaraka (self)", "AmK": "Amatyakaraka (career)", "BK": "Bhratrukaraka (siblings)",
        "MK": "Matrukaraka (mother)", "PiK": "Pitrukaraka (father)", "PK": "Putrakaraka (children)",
        "GK": "Gnatikaraka (relatives)", "DK": "Darakaraka (spouse)",
    }
    karaka_lookup = {b["karaka"]: b for b in core_bodies if b.get("karaka")}
    for code in karaka_order:
        b = karaka_lookup.get(code)
        if b:
            karaka_rows.append((code, karaka_names[code], BODY_FULLNAME_ASCII.get(b["key"], b["key"])))
    table(["Code", "Significance", "Graha"], karaka_rows, [22, 100, 56])

    # ---------------- Page 3: Graha positions ----------------
    pdf.add_page()
    banner("GRAHA POSITIONS", "Planetary Longitudes and Nakshatras")
    section("All Grahas & Special Lagnas")
    graha_rows = []
    for b in birth_chart["bodies"]:
        retro = "R" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
        combust = "C" if b.get("combust") else ""
        flags = " ".join(f for f in (retro, combust) if f) or "-"
        graha_rows.append((
            BODY_FULLNAME_ASCII.get(b["key"], b["key"]),
            f'{SIGNS_ASCII[b["sign"]]} {_fmt_deg_ascii(b["inSign"])}',
            f'{NAKSHATRAS_ASCII[b["nakIdx"]]} P{b["pada"]}',
            b.get("karaka") or "-",
            flags,
        ))
    table(["Graha", "Sign & Degree", "Nakshatra", "Karaka", "Flags"],
          graha_rows, [48, 42, 52, 22, 16], row_h=6.5)
    pdf.ln(2)
    pdf.set_font("Helvetica", "I", 8)
    pdf.set_text_color(*MUTED)
    pdf.cell(0, 5, "R = retrograde, C = combust (within orb of the Sun). "
                    "HL/BL/GL/SL/PP/ViL are special lagnas from Ishta Kala.", ln=True)

    # ---------------- Page 4: Vimsottari Mahadasha ----------------
    pdf.add_page()
    banner("VIMSOTTARI DASHA", "120-Year Planetary Period Timeline")
    section(f"Mahadasha Sequence  -  Starting Lord: {DASHA_LORDS_ASCII[birth_chart['dashas'][0]['lordIdx']]}")
    now_utc_ = datetime.utcnow()
    dasha_rows = []
    for d in birth_chart["dashas"]:
        active = "* current" if d["from"] <= now_utc_ < d["to"] else ""
        dasha_rows.append((
            DASHA_LORDS_ASCII[d["lordIdx"]],
            d["from"].strftime("%d %b %Y"),
            d["to"].strftime("%d %b %Y"),
            f'{d["yrs"]:.1f} yrs',
            active,
        ))
    table(["Lord", "From", "To", "Duration", ""], dasha_rows, [40, 40, 40, 30, 30], row_h=7)

    pdf.ln(6)
    pdf.set_font("Helvetica", "I", 8)
    pdf.set_text_color(*MUTED)
    pdf.multi_cell(0, 4.5,
        "Engine accuracy: Sun/Moon within a few arc-minutes, other grahas within roughly "
        "0.1-0.5 degrees, mean node (Rahu/Ketu). Generated by the Kundali app - Lahiri "
        "ayanamsa. For high-stakes decisions, cross-check against a Swiss-Ephemeris-based tool.")

    out = pdf.output(dest="S")
    return out.encode("latin-1") if isinstance(out, str) else bytes(out)


def generate_kundali_html_report(birth_chart, form) -> str:
    b_asc = next(b for b in birth_chart["bodies"] if b["key"] == "As")
    b_moon = next(b for b in birth_chart["bodies"] if b["key"] == "Mo")
    pan = birth_chart["panchanga"]
    core_bodies = [b for b in birth_chart["bodies"] if b["key"] in CORE_KEYS]

    header_pairs = [
        ("Name", form["name"] or "—"),
        ("Date of birth", form["dob"].strftime("%d %B %Y")),
        ("Time of birth", form["tob"].strftime("%H:%M:%S")),
        ("Place", f'{form["city"][0]}, {form["city"][1]}'),
        ("Ayanāṁśa", f"{fmt_deg(birth_chart['ayanDate'])} (Lahiri)"),
        ("Lagna", f"{SIGNS[b_asc['sign']]} {fmt_deg(b_asc['inSign'])}"),
        ("Moon sign", SIGNS[b_moon["sign"]]),
        ("Nakṣatra", f"{NAKSHATRAS[pan['nakIdx']]} · pada {pan['nakPada']}"),
        ("Vāra", pan["vara"]),
        ("Tithi", f"{pan['paksha']} {pan['tithiName']} · {pan['tithiPct']:.1f}%"),
        ("Yoga", YOGAS[pan["yogaIdx"]]),
        ("Karaṇa", pan["karana"]),
    ]
    header_rows = "".join(
        f"<tr><td class='k'>{k}</td><td class='v'>{v}</td></tr>" for k, v in header_pairs
    )

    graha_rows = "".join(
        f"<tr><td class='key'>{b['key']}</td><td>{b['name']}"
        f"{' <span class=\"retro\">℞</span>' if (b['retro'] and b['key'] not in ('Ra','Ke')) else ''}"
        f"{' <span class=\"combust\">🔥</span>' if b.get('combust') else ''}</td>"
        f"<td>{SIGN_ABBR[b['sign']]} {fmt_dms(b['inSign'])}</td>"
        f"<td>{NAKSHATRAS[b['nakIdx']]} P{b['pada']}</td>"
        f"<td>{b.get('karaka') or '—'}</td></tr>"
        for b in birth_chart["bodies"]
    )

    now_utc_ = datetime.utcnow()
    dasha_rows = "".join(
        f"<tr class=\"{'active' if d['from'] <= now_utc_ < d['to'] else ''}\">"
        f"<td>{d['lord']}</td><td>{d['from'].strftime('%d %b %Y')}</td>"
        f"<td>{d['to'].strftime('%d %b %Y')}</td><td>{d['yrs']:.1f} yrs</td></tr>"
        for d in birth_chart["dashas"]
    )

    # ---- CSS-only diamond (North-Indian) chart: 12 absolutely-positioned
    # house cells inside a rotated-square backdrop, matching the on-screen chart.
    by_house = [[] for _ in range(12)]
    for b in core_bodies:
        if b["key"] == "As":
            continue
        by_house[(b["sign"] - b_asc["sign"] + 12) % 12].append(b)
    house_positions = [
        (50, 15), (25, 7.5), (12.5, 25), (23, 50), (12.5, 75), (25, 92.5),
        (50, 74), (75, 92.5), (87.5, 75), (74, 50), (87.5, 25), (75, 7.5),
    ]
    house_cells = []
    for h, (left, top) in enumerate(house_positions):
        sign_num = ((b_asc["sign"] + h) % 12) + 1
        lines = [f'<div class="hnum">{sign_num}</div>']
        if h == 0:
            lines.append(f'<div class="asc">As {int(b_asc["inSign"])}°</div>')
        for b in by_house[h]:
            retro = "℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
            lines.append(f'<div class="pl">{b["key"]} {int(b["inSign"])}°{retro}</div>')
        house_cells.append(
            f'<div class="house" style="left:{left}%;top:{top}%;">{"".join(lines)}</div>'
        )
    chart_html = f"""
    <div class="chartwrap">
      <div class="diamond"></div>
      {"".join(house_cells)}
    </div>
    """

    return f"""<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>Kundali Report</title>
<style>
  body {{ font-family: Georgia, serif; max-width: 760px; margin: 0 auto; padding: 30px 24px 50px;
          color: #3A2E1F; background: #FFFDF3; }}
  .banner {{ background: #B8842E; color: #FFFDE7; padding: 18px 24px; border-radius: 10px;
             text-align: center; margin-bottom: 22px; }}
  .banner h1 {{ margin: 0; letter-spacing: 0.05em; }}
  .banner p {{ margin: 4px 0 0; font-size: 13px; opacity: 0.9; }}
  h2 {{ color: #B8842E; border-bottom: 2px solid #F0DE94; padding-bottom: 6px; margin-top: 34px; }}
  table {{ width: 100%; border-collapse: collapse; font-size: 14px; }}
  td {{ padding: 6px 10px; border-bottom: 1px solid #eee; }}
  td.k {{ color: #7A6F5C; width: 40%; }}
  td.v {{ font-weight: 600; }}
  tr:nth-child(even) td {{ background: #FFF9E2; }}
  tr.active td {{ background: #FFF3B0; font-weight: 700; }}
  .retro {{ color: #C4462B; font-size: 12px; }}
  .combust {{ font-size: 12px; }}
  .footer {{ color: #7A6F5C; font-size: 12px; margin-top: 30px; text-align: center; }}
  .chartwrap {{ position: relative; width: 420px; height: 420px; margin: 20px auto; }}
  .diamond {{ position: absolute; inset: 0; border: 2px solid #B8842E; border-radius: 4px;
              background:
                linear-gradient(135deg, transparent calc(50% - 0.75px), #B8842E calc(50% - 0.75px), #B8842E calc(50% + 0.75px), transparent calc(50% + 0.75px)),
                linear-gradient(45deg, transparent calc(50% - 0.75px), #B8842E calc(50% - 0.75px), #B8842E calc(50% + 0.75px), transparent calc(50% + 0.75px)),
                linear-gradient(#FFFDE7, #FFF3B0); }}
  .house {{ position: absolute; transform: translate(-50%, -50%); text-align: center;
            font-size: 11px; width: 90px; }}
  .hnum {{ color: #7A6F5C; font-size: 10px; }}
  .asc {{ color: #3A5B8C; font-weight: 700; }}
  .pl {{ font-weight: 700; }}
</style>
</head>
<body>
  <div class="banner">
    <h1>Kuṇḍalī</h1>
    <p>Vedic Birth Chart Report · Lahiri Ayanāṁśa</p>
  </div>

  <h2>Birth Details</h2>
  <table>{header_rows}</table>

  <h2>Rāśi Chart (D1) · North Indian Style</h2>
  {chart_html}

  <h2>Graha Positions</h2>
  <table>
    <tr><th>Graha</th><th>Name</th><th>Sign &amp; Degree</th><th>Nakṣatra</th><th>Kāraka</th></tr>
    {graha_rows}
  </table>

  <h2>Viṁśottarī Mahādaśā</h2>
  <table>
    <tr><th>Lord</th><th>From</th><th>To</th><th>Duration</th></tr>
    {dasha_rows}
  </table>

  <p class="footer">Generated by Kuṇḍalī · Lahiri ayanāṁśa engine · houses fixed to the birth lagna.<br>
  Engine accuracy: Sun/Moon within a few arc-minutes, other grahas ~0.1–0.5°, mean node.</p>
</body></html>
"""


# ============================================================
# RAZORPAY — real payments (Test Mode by default, safe to try)
# ============================================================
#
# Reads credentials from environment variables. On Render: your service ->
# Environment -> add RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET, APP_BASE_URL.
#
# TESTING (no real money moves, but every step is the real integration):
#   1. Dashboard -> toggle "Test Mode" (top-left) -> Settings -> API Keys
#      -> Generate Test Key. Copy the Key Id (rzp_test_...) and Key Secret.
#   2. Set RAZORPAY_KEY_ID / RAZORPAY_KEY_SECRET to those TEST values, and
#      APP_BASE_URL to this app's public URL (e.g. https://yourapp.onrender.com).
#   3. Click "Upgrade to Premium" in the app, then in the Razorpay checkout
#      modal pay with the official test card: 4111 1111 1111 1111, any
#      future expiry, any CVV, then any 4-10 digit OTP to succeed (a <4
#      digit OTP simulates a decline). For UPI, use the VPA "success@razorpay"
#      to simulate success or "failure@razorpay" to simulate a decline.
#   4. Check the Razorpay Dashboard -> Transactions (still in Test Mode) to
#      see the test payment land there in real time.
#   5. When ready for real money, swap in the rzp_live_... keys — nothing
#      else in this file needs to change.

RAZORPAY_KEY_ID = os.environ.get("RAZORPAY_KEY_ID", "")
RAZORPAY_KEY_SECRET = os.environ.get("RAZORPAY_KEY_SECRET", "")
APP_BASE_URL = os.environ.get("APP_BASE_URL", "").rstrip("/")
PREMIUM_PRICE_INR = 299
PREMIUM_PRICE_PAISE = PREMIUM_PRICE_INR * 100

RAZORPAY_CONFIGURED = bool(RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET and APP_BASE_URL)
RAZORPAY_TEST_MODE = RAZORPAY_KEY_ID.startswith("rzp_test_")


def razorpay_create_order(amount_paise: int, receipt: str) -> dict:
    """Creates a Razorpay Order server-side (using the secret key, never exposed to
    the browser). Raises requests.HTTPError on failure."""
    resp = requests.post(
        "https://api.razorpay.com/v1/orders",
        auth=(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET),
        json={
            "amount": amount_paise,
            "currency": "INR",
            "receipt": receipt,
            "payment_capture": 1,  # auto-capture on successful payment
        },
        timeout=15,
    )
    resp.raise_for_status()
    return resp.json()


def razorpay_verify_signature(order_id: str, payment_id: str, signature: str) -> bool:
    """Standard Razorpay Checkout signature check: HMAC-SHA256 of
    'order_id|payment_id' using the account's key secret. This is what proves
    the success callback actually came from a completed Razorpay payment and
    wasn't just typed into the URL bar."""
    msg = f"{order_id}|{payment_id}".encode("utf-8")
    expected = hmac.new(RAZORPAY_KEY_SECRET.encode("utf-8"), msg, hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected, signature)


def render_razorpay_checkout(order_id: str, amount_paise: int, user_name: str, username: str):
    """Opens the Razorpay Checkout modal immediately and, on success, redirects the
    top-level browser back to this app with the payment proof in the query string
    so Streamlit can verify it server-side on the next run."""
    success_url = f"{APP_BASE_URL}/?rzp_order_id={order_id}"
    st.components.v1.html(
        f"""
        <script src="https://checkout.razorpay.com/v1/checkout.js"></script>
        <div id="rzp-status" style="font-family:Georgia, serif; color:#7A6F5C; padding:10px 0;">
            Opening secure Razorpay checkout…
        </div>
        <script>
        var options = {{
            "key": "{RAZORPAY_KEY_ID}",
            "amount": "{amount_paise}",
            "currency": "INR",
            "name": "Kuṇḍalī",
            "description": "Premium Kundali report",
            "order_id": "{order_id}",
            "prefill": {{ "name": "{user_name or username}" }},
            "theme": {{ "color": "#B8842E" }},
            "handler": function (response) {{
                var url = "{success_url}"
                    + "&rzp_payment_id=" + encodeURIComponent(response.razorpay_payment_id)
                    + "&rzp_signature=" + encodeURIComponent(response.razorpay_signature);
                window.top.location.href = url;
            }},
            "modal": {{
                "ondismiss": function () {{
                    document.getElementById("rzp-status").innerText =
                        "Checkout closed — click 'Reopen payment window' below to retry.";
                }}
            }}
        }};
        var rzp = new Razorpay(options);
        rzp.on('payment.failed', function (response) {{
            document.getElementById("rzp-status").innerText =
                "Payment failed: " + response.error.description;
        }});
        rzp.open();
        </script>
       """,
        height=700,
        scrolling=True,
    )


def handle_razorpay_return():
    """Runs on every rerun, before anything else, so a payment redirect is verified
    and applied exactly once even if the page is refreshed afterwards. Deliberately
    does NOT depend on st.session_state['user'] being present — a full-page
    redirect back from Razorpay can land in a fresh browser session, so the
    account to credit comes from the payments ledger (order_owner), not from
    whoever happens to be logged in on this particular run."""
    params = st.query_params
    order_id = params.get("rzp_order_id")
    payment_id = params.get("rzp_payment_id")
    signature = params.get("rzp_signature")
    if not (order_id and payment_id and signature):
        return
    if payment_already_verified(payment_id):
        st.query_params.clear()
        return
    if not razorpay_verify_signature(order_id, payment_id, signature):
        st.query_params.clear()
        st.error("Payment verification failed — signature mismatch. If you were charged, "
                  "contact support with your payment ID: " + payment_id)
        return
    owner = order_owner(order_id)
    if owner is None:
        st.query_params.clear()
        st.error("Payment verified but no matching order was found. Contact support with "
                  "payment ID: " + payment_id)
        return
    if mark_order_paid(order_id, payment_id):
        set_premium(owner["user_id"], True)
        st.query_params.clear()
        st.session_state.pop("checkout_order_id", None)
        st.session_state.pop("checkout_rendered_for", None)
        st.session_state["just_upgraded"] = True
        st.rerun()
    else:
        st.query_params.clear()


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

handle_razorpay_return()
if st.session_state.pop("just_upgraded", False):
    st.success("Payment verified — premium unlocked! 🎉")

topbar_l, topbar_r = st.columns([4, 1])
with topbar_l:
    st.markdown(
        f'<h1 style="color:{C["gold"]}; font-family:Georgia, serif; letter-spacing:0.06em;">Kuṇḍalī</h1>'
        f'<p class="kmuted" style="margin-top:-10px; font-size:18px;">Vedic birth-chart engine · Lahiri ayanamsa · Python build</p>',
        unsafe_allow_html=True,
    )
with topbar_r:
    st.markdown("<br>", unsafe_allow_html=True)
    premium_badge = " · ⭐ Premium" if is_premium(st.session_state["user"]["id"]) else ""
    st.markdown(f'<p class="kmuted" style="text-align:right;">Signed in as <b>{st.session_state["user"]["username"]}</b>{premium_badge}</p>', unsafe_allow_html=True)
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
    # st.time_input's native browser widget often only allows clicking spinner
    # arrows, not typing digits directly. Plain number_input boxes are always
    # typable, so hour/minute/second are entered as three separate fields
    # and combined into a time object below.
    default_tob = dtime.fromisoformat(saved_profile["tob"]) if (saved_profile and saved_profile.get("tob")) else dtime(12, 16, 0)
    st.markdown('<p style="margin-bottom:2px;">Time (24h, local)</p>', unsafe_allow_html=True)
    th_col, tm_col, ts_col = st.columns(3)
    with th_col:
        tob_hour = st.number_input(
            "Hour", min_value=0, max_value=23, value=default_tob.hour, step=1, key="tob_hour"
        )
    with tm_col:
        tob_minute = st.number_input(
            "Minute", min_value=0, max_value=59, value=default_tob.minute, step=1, key="tob_minute"
        )
    with ts_col:
        tob_second = st.number_input(
            "Second", min_value=0, max_value=59, value=default_tob.second, step=1, key="tob_second"
        )
    tob = dtime(int(tob_hour), int(tob_minute), int(tob_second))

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
    ss=form["tob"].second,
)

refresh = st.button("🔄 Refresh transits (updates to current time)")
now_local = now_in_city(tz)
transit_chart = compute_chart(
    now_local.year, now_local.month, now_local.day,
    now_local.hour, now_local.minute, lat, lon, tz,
    ss=now_local.second,
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

# ---- Premium: paid Kundali report (PDF, with HTML fallback) ---------------
user_id = st.session_state["user"]["id"]
st.markdown(f'<div class="kcard" style="border:2px solid {C["gold"]};">', unsafe_allow_html=True)
if is_premium(user_id):
    st.markdown(
        '<h4>⭐ Premium — Your Kundali Report</h4>'
        '<p class="kmuted">You have premium access. Download your full report: birth details, '
        'Pañcāṅga, graha positions, and the Viṁśottarī daśā timeline.</p>',
        unsafe_allow_html=True,
    )
    if HAS_FPDF:
        pdf_bytes = generate_kundali_pdf_bytes(birth_chart, form)
        st.download_button(
            "📄 Download Kundali PDF", data=pdf_bytes,
            file_name=f"kundali_{form['city'][0]}_{form['dob'].isoformat()}.pdf",
            mime="application/pdf", use_container_width=True,
        )
    else:
        st.info("Install `fpdf2` (`pip install fpdf2`) to enable PDF export. "
                "Meanwhile, here's an HTML report you can save or print to PDF from your browser.")
        html_report = generate_kundali_html_report(birth_chart, form)
        st.download_button(
            "📄 Download Kundali Report (HTML)", data=html_report,
            file_name=f"kundali_{form['city'][0]}_{form['dob'].isoformat()}.html",
            mime="text/html", use_container_width=True,
        )
else:
    st.markdown(
        '<h4>⭐ Go Premium — Get Your Kundali Report</h4>'
        '<p class="kmuted">Unlock a downloadable Kundali report (birth details, graha positions, '
        'and Viṁśottarī daśā timeline) for a one-time payment.</p>',
        unsafe_allow_html=True,
    )
    if not RAZORPAY_CONFIGURED:
        st.warning(
            "Payments aren't configured yet. Set the environment variables "
            "**RAZORPAY_KEY_ID**, **RAZORPAY_KEY_SECRET**, and **APP_BASE_URL** "
            "(e.g. `https://yourdomain.com`) in your Render service settings, then redeploy. "
            "Use `rzp_test_...` keys first to try the whole flow safely — see the setup "
            "comment above `RAZORPAY_KEY_ID` in the code for exact steps and test-card numbers."
        )
    else:
        if RAZORPAY_TEST_MODE:
            st.info("🧪 Test Mode is active (rzp_test_ key) — payments here use fake money. "
                     "Card `4111 1111 1111 1111`, any future expiry/CVV, then any 4-10 digit OTP "
                     "to succeed. For UPI use `success@razorpay`. Nothing is actually charged.")
        pcol1, pcol2 = st.columns([1, 1])
        with pcol1:
            st.markdown(
                f'<p style="font-size:28px;font-weight:700;color:{C["gold"]};margin-bottom:0;">₹{PREMIUM_PRICE_INR}</p>'
                f'<p class="kmuted" style="margin-top:0;">one-time · lifetime access to report downloads</p>',
                unsafe_allow_html=True,
            )
        with pcol2:
            st.markdown("<br>", unsafe_allow_html=True)
            if st.button("Upgrade to Premium", use_container_width=True, key="start_checkout"):
                try:
                    order = razorpay_create_order(
                        PREMIUM_PRICE_PAISE, receipt=f"user{user_id}-{int(time.time())}"
                    )
                    record_order(user_id, order["id"], PREMIUM_PRICE_PAISE)
                    st.session_state["checkout_order_id"] = order["id"]
                    st.session_state.pop("checkout_rendered_for", None)
                except requests.HTTPError as e:
                    st.error(f"Couldn't start checkout — Razorpay rejected the request: {e}")
                except requests.RequestException as e:
                    st.error(f"Couldn't reach Razorpay — check your connection and try again. ({e})")

        # If we have a live order in flight, open the actual Razorpay Checkout modal —
        # but only render/open it ONCE per order, otherwise any unrelated widget
        # interaction elsewhere on the page (which triggers a Streamlit rerun) would
        # pop the modal open again every single time.
        pending_order_id = st.session_state.get("checkout_order_id")
        if pending_order_id:
            if st.session_state.get("checkout_rendered_for") != pending_order_id:
                render_razorpay_checkout(
                    pending_order_id, PREMIUM_PRICE_PAISE,
                    form.get("name", ""), st.session_state["user"]["username"],
                )
                st.session_state["checkout_rendered_for"] = pending_order_id
            else:
                rcol1, rcol2 = st.columns([1, 1])
                with rcol1:
                    if st.button("Reopen payment window", use_container_width=True, key="reopen_checkout"):
                        st.session_state["checkout_rendered_for"] = None
                        st.rerun()
                with rcol2:
                    if st.button("Cancel", use_container_width=True, key="cancel_checkout"):
                        st.session_state.pop("checkout_order_id", None)
                        st.session_state.pop("checkout_rendered_for", None)
                        st.rerun()
        st.caption("Secured by Razorpay · UPI, cards, netbanking, and wallets accepted.")
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
