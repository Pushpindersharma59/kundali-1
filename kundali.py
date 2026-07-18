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

# short 2-letter codes, in the same order as DASHA_LORDS (used for nakshatra-lord + dasha display)
DASHA_LORD_SHORT = ["Ke", "Ve", "Su", "Mo", "Ma", "Ra", "Jp", "Sa", "Me"]

SIGN_ABBR = ["Ar", "Ta", "Ge", "Cn", "Le", "Vi", "Li", "Sc", "Sg", "Cp", "Aq", "Pi"]

NAK_ABBR = ["Aśw", "Bha", "Krt", "Roh", "Mrg", "Ard", "Pun", "Pus", "Āśl", "Mag", "PPh",
            "UPh", "Has", "Cit", "Swa", "Vis", "Anu", "Jye", "Mūl", "PAs", "UAs", "Śra",
            "Dha", "Śat", "PBh", "UBh", "Rev"]

# combustion orb in degrees (approx. classical values) — used only for the 🔥 marker
COMBUSTION_ORB = {"Ma": 17, "Me": 14, "Jp": 11, "Ve": 10, "Sa": 15}

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
     ("Port Blair", "Andaman and Nicobar Islands, India", 11.6234, 92.7265, 5.5),
    ("Adoni", "Andhra Pradesh, India", 15.6279, 77.2749, 5.5),
    ("Amalapuram", "Andhra Pradesh, India", 16.5787, 82.0061, 5.5),
    ("Anakapalle", "Andhra Pradesh, India", 17.6913, 83.0039, 5.5),
    ("Anantapur", "Andhra Pradesh, India", 14.6819, 77.6006, 5.5),
    ("Bapatla", "Andhra Pradesh, India", 15.9042, 80.4675, 5.5),
    ("Bhimavaram", "Andhra Pradesh, India", 16.5449, 81.5212, 5.5),
    ("Chilakaluripet", "Andhra Pradesh, India", 16.0899, 80.1671, 5.5),
    ("Chittoor", "Andhra Pradesh, India", 13.2172, 79.1003, 5.5),
    ("Dharmavaram", "Andhra Pradesh, India", 14.4143, 77.7204, 5.5),
    ("Eluru", "Andhra Pradesh, India", 16.7107, 81.0952, 5.5),
    ("Gudivada", "Andhra Pradesh, India", 16.4419, 80.9955, 5.5),
    ("Gudur", "Andhra Pradesh, India", 14.1463, 79.8504, 5.5),
    ("Guntur", "Andhra Pradesh, India", 16.3067, 80.4365, 5.5),
    ("Hindupur", "Andhra Pradesh, India", 13.8281, 77.4914, 5.5),
    ("Kadapa", "Andhra Pradesh, India", 14.4673, 78.8242, 5.5),
    ("Kakinada", "Andhra Pradesh, India", 16.9891, 82.2475, 5.5),
    ("Kavali", "Andhra Pradesh, India", 14.9132, 79.9930, 5.5),
    ("Kurnool", "Andhra Pradesh, India", 15.8281, 78.0373, 5.5),
    ("Machilipatnam", "Andhra Pradesh, India", 16.1875, 81.1389, 5.5),
    ("Madanapalle", "Andhra Pradesh, India", 13.5503, 78.5029, 5.5),
    ("Mangalagiri", "Andhra Pradesh, India", 16.4308, 80.5681, 5.5),
    ("Nandyal", "Andhra Pradesh, India", 15.4786, 78.4831, 5.5),
    ("Narasaraopet", "Andhra Pradesh, India", 16.2360, 80.0479, 5.5),
    ("Nellore", "Andhra Pradesh, India", 14.4426, 79.9865, 5.5),
    ("Ongole", "Andhra Pradesh, India", 15.5057, 80.0499, 5.5),
    ("Proddatur", "Andhra Pradesh, India", 14.7502, 78.5481, 5.5),
    ("Rajahmundry", "Andhra Pradesh, India", 17.0005, 81.8040, 5.5),
    ("Srikakulam", "Andhra Pradesh, India", 18.2969, 83.8976, 5.5),
    ("Tadepalligudem", "Andhra Pradesh, India", 16.8147, 81.5278, 5.5),
    ("Tadipatri", "Andhra Pradesh, India", 14.9070, 78.0107, 5.5),
    ("Tenali", "Andhra Pradesh, India", 16.2430, 80.6400, 5.5),
    ("Tirupati", "Andhra Pradesh, India", 13.6288, 79.4192, 5.5),
    ("Vijayawada", "Andhra Pradesh, India", 16.5062, 80.6480, 5.5),
    ("Visakhapatnam", "Andhra Pradesh, India", 17.6868, 83.2185, 5.5),
    ("Vizianagaram", "Andhra Pradesh, India", 18.1067, 83.3956, 5.5),
    ("Itanagar", "Arunachal Pradesh, India", 27.0844, 93.6053, 5.5),
    ("Naharlagun", "Arunachal Pradesh, India", 27.1047, 93.6952, 5.5),
    ("Pasighat", "Arunachal Pradesh, India", 28.0667, 95.3333, 5.5),
    ("Tawang", "Arunachal Pradesh, India", 27.5860, 91.8656, 5.5),
    ("Dibrugarh", "Assam, India", 27.4728, 94.9120, 5.5),
    ("Dhubri", "Assam, India", 26.0186, 89.9856, 5.5),
    ("Goalpara", "Assam, India", 26.1680, 90.6250, 5.5),
    ("Golaghat", "Assam, India", 26.5230, 93.9595, 5.5),
    ("Guwahati", "Assam, India", 26.1445, 91.7362, 5.5),
    ("Jorhat", "Assam, India", 26.7509, 94.2037, 5.5),
    ("Karimganj", "Assam, India", 24.8647, 92.3592, 5.5),
    ("Nagaon", "Assam, India", 26.3480, 92.6840, 5.5),
    ("Silchar", "Assam, India", 24.8333, 92.7789, 5.5),
    ("Tezpur", "Assam, India", 26.6528, 92.7926, 5.5),
    ("Tinsukia", "Assam, India", 27.4891, 95.3599, 5.5),
    ("Ara", "Bihar, India", 25.5560, 84.6633, 5.5),
    ("Arrah", "Bihar, India", 25.5560, 84.6633, 5.5),
    ("Aurangabad", "Bihar, India", 24.7520, 84.3742, 5.5),
    ("Begusarai", "Bihar, India", 25.4182, 86.1272, 5.5),
    ("Bettiah", "Bihar, India", 26.8028, 84.5031, 5.5),
    ("Bhagalpur", "Bihar, India", 25.2425, 86.9842, 5.5),
    ("Bihar Sharif", "Bihar, India", 25.1975, 85.5237, 5.5),
    ("Buxar", "Bihar, India", 25.5647, 83.9777, 5.5),
    ("Chapra", "Bihar, India", 25.7796, 84.7499, 5.5),
    ("Darbhanga", "Bihar, India", 26.1542, 85.8918, 5.5),
    ("Dehri", "Bihar, India", 24.9277, 84.1823, 5.5),
    ("Gaya", "Bihar, India", 24.7914, 85.0002, 5.5),
    ("Hajipur", "Bihar, India", 25.6927, 85.2081, 5.5),
    ("Jamalpur", "Bihar, India", 25.3127, 86.4889, 5.5),
    ("Jehanabad", "Bihar, India", 25.2137, 84.9873, 5.5),
    ("Katihar", "Bihar, India", 25.5420, 87.5620, 5.5),
    ("Kishanganj", "Bihar, India", 26.1022, 87.9523, 5.5),
    ("Motihari", "Bihar, India", 26.6486, 84.9166, 5.5),
    ("Munger", "Bihar, India", 25.3748, 86.4746, 5.5),
    ("Muzaffarpur", "Bihar, India", 26.1209, 85.3647, 5.5),
    ("Patna", "Bihar, India", 25.5941, 85.1376, 5.5),
    ("Purnia", "Bihar, India", 25.7771, 87.4753, 5.5),
    ("Saharsa", "Bihar, India", 25.8840, 86.6050, 5.5),
    ("Samastipur", "Bihar, India", 25.8620, 85.7795, 5.5),
    ("Sasaram", "Bihar, India", 24.9490, 84.0164, 5.5),
    ("Siwan", "Bihar, India", 26.2196, 84.3561, 5.5),
    ("Bilaspur", "Chhattisgarh, India", 22.0797, 82.1409, 5.5),
    ("Bhilai", "Chhattisgarh, India", 21.1938, 81.3509, 5.5),
    ("Dhamtari", "Chhattisgarh, India", 20.7074, 81.5497, 5.5),
    ("Durg", "Chhattisgarh, India", 21.1904, 81.2849, 5.5),
    ("Jagdalpur", "Chhattisgarh, India", 19.0741, 82.0080, 5.5),
    ("Korba", "Chhattisgarh, India", 22.3595, 82.7501, 5.5),
    ("Raigarh", "Chhattisgarh, India", 21.8974, 83.3956, 5.5),
    ("Raipur", "Chhattisgarh, India", 21.2514, 81.6296, 5.5),
    ("Rajnandgaon", "Chhattisgarh, India", 21.0974, 81.0337, 5.5),
    ("Margao", "Goa, India", 15.2993, 73.9580, 5.5),
    ("Mapusa", "Goa, India", 15.5937, 73.8132, 5.5),
    ("Panaji", "Goa, India", 15.4909, 73.8278, 5.5),
    ("Ponda", "Goa, India", 15.4030, 74.0155, 5.5),
    ("Ahmedabad", "Gujarat, India", 23.0225, 72.5714, 5.5),
    ("Amreli", "Gujarat, India", 21.6032, 71.2221, 5.5),
    ("Anand", "Gujarat, India", 22.5645, 72.9289, 5.5),
    ("Bhavnagar", "Gujarat, India", 21.7645, 72.1519, 5.5),
    ("Bhuj", "Gujarat, India", 23.2420, 69.6669, 5.5),
    ("Bharuch", "Gujarat, India", 21.7051, 72.9959, 5.5),
    ("Gandhidham", "Gujarat, India", 23.0753, 70.1337, 5.5),
    ("Gandhinagar", "Gujarat, India", 23.2156, 72.6369, 5.5),
    ("Godhra", "Gujarat, India", 22.7788, 73.6143, 5.5),
    ("Jamnagar", "Gujarat, India", 22.4707, 70.0577, 5.5),
    ("Junagadh", "Gujarat, India", 21.5222, 70.4579, 5.5),
    ("Mehsana", "Gujarat, India", 23.5880, 72.3693, 5.5),
    ("Morbi", "Gujarat, India", 22.8173, 70.8377, 5.5),
    ("Nadiad", "Gujarat, India", 22.6916, 72.8634, 5.5),
    ("Navsari", "Gujarat, India", 20.9467, 72.9520, 5.5),
    ("Palanpur", "Gujarat, India", 24.1722, 72.4383, 5.5),
    ("Patan", "Gujarat, India", 23.8500, 72.1167, 5.5),
    ("Porbandar", "Gujarat, India", 21.6417, 69.6293, 5.5),
    ("Rajkot", "Gujarat, India", 22.3039, 70.8022, 5.5),
    ("Surat", "Gujarat, India", 21.1702, 72.8311, 5.5),
    ("Surendranagar", "Gujarat, India", 22.7271, 71.6486, 5.5),
    ("Vadodara", "Gujarat, India", 22.3072, 73.1812, 5.5),
    ("Valsad", "Gujarat, India", 20.5992, 72.9342, 5.5),
    ("Veraval", "Gujarat, India", 20.9077, 70.3679, 5.5),
    ("Vapi", "Gujarat, India", 20.3893, 72.9106, 5.5),
    ("Ambala", "Haryana, India", 30.3782, 76.7767, 5.5),
    ("Bahadurgarh", "Haryana, India", 28.6929, 76.9356, 5.5),
    ("Bhiwani", "Haryana, India", 28.7930, 76.1397, 5.5),
    ("Charkhi Dadri", "Haryana, India", 28.5921, 76.2711, 5.5),
    ("Faridabad", "Haryana, India", 28.4089, 77.3178, 5.5),
    ("Fatehabad", "Haryana, India", 29.5152, 75.4553, 5.5),
    ("Gohana", "Haryana, India", 29.1378, 76.7033, 5.5),
    ("Gurugram", "Haryana, India", 28.4595, 77.0266, 5.5),
    ("Hisar", "Haryana, India", 29.1492, 75.7217, 5.5),
    ("Jhajjar", "Haryana, India", 28.6063, 76.6565, 5.5),
    ("Jind", "Haryana, India", 29.3167, 76.3167, 5.5),
    ("Kaithal", "Haryana, India", 29.8014, 76.3998, 5.5),
    ("Karnal", "Haryana, India", 29.6857, 76.9905, 5.5),
    ("Kurukshetra", "Haryana, India", 29.9695, 76.8783, 5.5),
    ("Mahendragarh", "Haryana, India", 28.2738, 76.1522, 5.5),
    ("Narnaul", "Haryana, India", 28.0444, 76.1083, 5.5),
    ("Palwal", "Haryana, India", 28.1447, 77.3255, 5.5),
    ("Panchkula", "Haryana, India", 30.6942, 76.8606, 5.5),
    ("Panipat", "Haryana, India", 29.3909, 76.9635, 5.5),
    ("Pehowa", "Haryana, India", 29.9789, 76.5820, 5.5),
    ("Rewari", "Haryana, India", 28.1990, 76.6183, 5.5),
    ("Rohtak", "Haryana, India", 28.8955, 76.6066, 5.5),
    ("Sirsa", "Haryana, India", 29.5349, 75.0289, 5.5),
    ("Sonipat", "Haryana, India", 28.9931, 77.0151, 5.5),
    ("Yamunanagar", "Haryana, India", 30.1290, 77.2674, 5.5),
    ("Baddi", "Himachal Pradesh, India", 30.9578, 76.7914, 5.5),
    ("Bilaspur", "Himachal Pradesh, India", 31.3315, 76.7566, 5.5),
    ("Chamba", "Himachal Pradesh, India", 32.5530, 76.1258, 5.5),
    ("Dharamshala", "Himachal Pradesh, India", 32.2190, 76.3234, 5.5),
    ("Hamirpur", "Himachal Pradesh, India", 31.6862, 76.5213, 5.5),
    ("Kangra", "Himachal Pradesh, India", 32.0998, 76.2691, 5.5),
    ("Kullu", "Himachal Pradesh, India", 31.9579, 77.1095, 5.5),
    ("Mandi", "Himachal Pradesh, India", 31.7084, 76.9314, 5.5),
    ("Nahan", "Himachal Pradesh, India", 30.5603, 77.2963, 5.5),
    ("Palampur", "Himachal Pradesh, India", 32.1107, 76.5366, 5.5),
    ("Shimla", "Himachal Pradesh, India", 31.1048, 77.1734, 5.5),
    ("Solan", "Himachal Pradesh, India", 30.9045, 77.0967, 5.5),
    ("Una", "Himachal Pradesh, India", 31.4646, 76.2691, 5.5),
    ("Anantnag", "Jammu and Kashmir, India", 33.7311, 75.1480, 5.5),
    ("Baramulla", "Jammu and Kashmir, India", 34.1980, 74.3636, 5.5),
    ("Budgam", "Jammu and Kashmir, India", 34.0150, 74.7220, 5.5),
    ("Ganderbal", "Jammu and Kashmir, India", 34.2300, 74.7800, 5.5),
    ("Jammu", "Jammu and Kashmir, India", 32.7266, 74.8570, 5.5),
    ("Kathua", "Jammu and Kashmir, India", 32.3694, 75.5254, 5.5),
    ("Kupwara", "Jammu and Kashmir, India", 34.5268, 74.2573, 5.5),
    ("Pulwama", "Jammu and Kashmir, India", 33.8740, 74.8990, 5.5),
    ("Samba", "Jammu and Kashmir, India", 32.5624, 75.1195, 5.5),
    ("Shopian", "Jammu and Kashmir, India", 33.7152, 74.8336, 5.5),
    ("Srinagar", "Jammu and Kashmir, India", 34.0837, 74.7973, 5.5),
    ("Udhampur", "Jammu and Kashmir, India", 32.9243, 75.1357, 5.5),
    ("Bokaro", "Jharkhand, India", 23.6693, 86.1511, 5.5),
    ("Chaibasa", "Jharkhand, India", 22.5500, 85.8000, 5.5),
    ("Deoghar", "Jharkhand, India", 24.4829, 86.6947, 5.5),
    ("Dhanbad", "Jharkhand, India", 23.7957, 86.4304, 5.5),
    ("Dumka", "Jharkhand, India", 24.2678, 87.2486, 5.5),
    ("Giridih", "Jharkhand, India", 24.1821, 86.3022, 5.5),
    ("Godda", "Jharkhand, India", 24.8255, 87.2123, 5.5),
    ("Hazaribagh", "Jharkhand, India", 23.9966, 85.3691, 5.5),
    ("Jamshedpur", "Jharkhand, India", 22.8046, 86.2029, 5.5),
    ("Khunti", "Jharkhand, India", 23.0760, 85.2780, 5.5),
    ("Medininagar", "Jharkhand, India", 24.0390, 84.0730, 5.5),
    ("Ramgarh", "Jharkhand, India", 23.6303, 85.5216, 5.5),
    ("Ranchi", "Jharkhand, India", 23.3441, 85.3096, 5.5),
    ("Sahibganj", "Jharkhand, India", 25.2500, 87.6500, 5.5),
    ("Bagalkot", "Karnataka, India", 16.1867, 75.6961, 5.5),
    ("Ballari", "Karnataka, India", 15.1394, 76.9214, 5.5),
    ("Belagavi", "Karnataka, India", 15.8497, 74.4977, 5.5),
    ("Bengaluru", "Karnataka, India", 12.9716, 77.5946, 5.5),
    ("Bidar", "Karnataka, India", 17.9133, 77.5301, 5.5),
    ("Chikkamagaluru", "Karnataka, India", 13.3161, 75.7720, 5.5),
    ("Chitradurga", "Karnataka, India", 14.2306, 76.3980, 5.5),
    ("Davanagere", "Karnataka, India", 14.4644, 75.9218, 5.5),
    ("Dharwad", "Karnataka, India", 15.4589, 75.0078, 5.5),
    ("Gadag", "Karnataka, India", 15.4310, 75.6350, 5.5),
    ("Hassan", "Karnataka, India", 13.0072, 76.0963, 5.5),
    ("Hubballi", "Karnataka, India", 15.3647, 75.1240, 5.5),
    ("Kalaburagi", "Karnataka, India", 17.3297, 76.8343, 5.5),
    ("Kolar", "Karnataka, India", 13.1367, 78.1299, 5.5),
    ("Mandya", "Karnataka, India", 12.5223, 76.8975, 5.5),
    ("Mangaluru", "Karnataka, India", 12.9141, 74.8560, 5.5),
    ("Mysuru", "Karnataka, India", 12.2958, 76.6394, 5.5),
    ("Raichur", "Karnataka, India", 16.2076, 77.3463, 5.5),
    ("Ramanagara", "Karnataka, India", 12.7219, 77.2815, 5.5),
    ("Shivamogga", "Karnataka, India", 13.9299, 75.5681, 5.5),
    ("Tumakuru", "Karnataka, India", 13.3409, 77.1010, 5.5),
    ("Udupi", "Karnataka, India", 13.3409, 74.7421, 5.5),
    ("Vijayapura", "Karnataka, India", 16.8302, 75.7100, 5.5),
    ("Yadgir", "Karnataka, India", 16.7700, 77.1400, 5.5),
    ("Alappuzha", "Kerala, India", 9.4981, 76.3388, 5.5),
    ("Angamaly", "Kerala, India", 10.1900, 76.3900, 5.5),
    ("Chalakudy", "Kerala, India", 10.3000, 76.3400, 5.5),
    ("Ernakulam", "Kerala, India", 9.9816, 76.2999, 5.5),
    ("Idukki", "Kerala, India", 9.8500, 76.9700, 5.5),
    ("Kannur", "Kerala, India", 11.8745, 75.3704, 5.5),
    ("Kasaragod", "Kerala, India", 12.4996, 74.9869, 5.5),
    ("Kochi", "Kerala, India", 9.9312, 76.2673, 5.5),
    ("Kollam", "Kerala, India", 8.8932, 76.6141, 5.5),
    ("Kottayam", "Kerala, India", 9.5916, 76.5222, 5.5),
    ("Kozhikode", "Kerala, India", 11.2588, 75.7804, 5.5),
    ("Malappuram", "Kerala, India", 11.0730, 76.0740, 5.5),
    ("Muvattupuzha", "Kerala, India", 9.9790, 76.5770, 5.5),
    ("Palakkad", "Kerala, India", 10.7867, 76.6548, 5.5),
    ("Pathanamthitta", "Kerala, India", 9.2648, 76.7870, 5.5),
    ("Perinthalmanna", "Kerala, India", 10.9710, 76.2260, 5.5),
    ("Thalassery", "Kerala, India", 11.7488, 75.4929, 5.5),
    ("Thrissur", "Kerala, India", 10.5276, 76.2144, 5.5),
    ("Thiruvananthapuram", "Kerala, India", 8.5241, 76.9366, 5.5),
    ("Tirur", "Kerala, India", 10.9137, 75.9220, 5.5),
    ("Vadakara", "Kerala, India", 11.6085, 75.5917, 5.5),
    ("Balaghat", "Madhya Pradesh, India", 21.8129, 80.1838, 5.5),
    ("Betul", "Madhya Pradesh, India", 21.9000, 77.9000, 5.5),
    ("Bhind", "Madhya Pradesh, India", 26.5667, 78.7833, 5.5),
    ("Bhopal", "Madhya Pradesh, India", 23.2599, 77.4126, 5.5),
    ("Burhanpur", "Madhya Pradesh, India", 21.3074, 76.2303, 5.5),
    ("Chhatarpur", "Madhya Pradesh, India", 24.9142, 79.5883, 5.5),
    ("Chhindwara", "Madhya Pradesh, India", 22.0574, 78.9382, 5.5),
    ("Damoh", "Madhya Pradesh, India", 23.8333, 79.4500, 5.5),
    ("Datia", "Madhya Pradesh, India", 25.6731, 78.4591, 5.5),
    ("Dewas", "Madhya Pradesh, India", 22.9659, 76.0553, 5.5),
    ("Dhar", "Madhya Pradesh, India", 22.6013, 75.3025, 5.5),
    ("Guna", "Madhya Pradesh, India", 24.6500, 77.3167, 5.5),
    ("Gwalior", "Madhya Pradesh, India", 26.2183, 78.1828, 5.5),
    ("Hoshangabad", "Madhya Pradesh, India", 22.7500, 77.7200, 5.5),
    ("Indore", "Madhya Pradesh, India", 22.7196, 75.8577, 5.5),
    ("Jabalpur", "Madhya Pradesh, India", 23.1815, 79.9864, 5.5),
    ("Katni", "Madhya Pradesh, India", 23.8388, 80.3945, 5.5),
    ("Khandwa", "Madhya Pradesh, India", 21.8247, 76.3526, 5.5),
    ("Khargone", "Madhya Pradesh, India", 21.8225, 75.6146, 5.5),
    ("Mandsaur", "Madhya Pradesh, India", 24.0735, 75.0699, 5.5),
    ("Morena", "Madhya Pradesh, India", 26.4947, 77.9953, 5.5),
    ("Narsinghpur", "Madhya Pradesh, India", 22.9496, 79.1945, 5.5),
    ("Neemuch", "Madhya Pradesh, India", 24.4734, 74.8718, 5.5),
    ("Panna", "Madhya Pradesh, India", 24.7200, 80.1900, 5.5),
    ("Ratlam", "Madhya Pradesh, India", 23.3342, 75.0376, 5.5),
    ("Rewa", "Madhya Pradesh, India", 24.5362, 81.3037, 5.5),
    ("Sagar", "Madhya Pradesh, India", 23.8388, 78.7378, 5.5),
    ("Satna", "Madhya Pradesh, India", 24.6005, 80.8322, 5.5),
    ("Sehore", "Madhya Pradesh, India", 23.2000, 77.0800, 5.5),
    ("Shahdol", "Madhya Pradesh, India", 23.3000, 81.3500, 5.5),
    ("Shivpuri", "Madhya Pradesh, India", 25.4320, 77.6644, 5.5),
    ("Singrauli", "Madhya Pradesh, India", 24.2000, 82.6700, 5.5),
    ("Tikamgarh", "Madhya Pradesh, India", 24.7400, 78.8300, 5.5),
    ("Ujjain", "Madhya Pradesh, India", 23.1765, 75.7885, 5.5),
    ("Vidisha", "Madhya Pradesh, India", 23.5251, 77.8081, 5.5),
    ("Ahmednagar", "Maharashtra, India", 19.0948, 74.7480, 5.5),
    ("Akola", "Maharashtra, India", 20.7002, 77.0082, 5.5),
    ("Amravati", "Maharashtra, India", 20.9374, 77.7796, 5.5),
    ("Aurangabad", "Maharashtra, India", 19.8762, 75.3433, 5.5),
    ("Baramati", "Maharashtra, India", 18.1500, 74.5800, 5.5),
    ("Beed", "Maharashtra, India", 18.9891, 75.7601, 5.5),
    ("Bhandara", "Maharashtra, India", 21.1702, 79.6500, 5.5),
    ("Bhiwandi", "Maharashtra, India", 19.3002, 73.0588, 5.5),
    ("Chandrapur", "Maharashtra, India", 19.9615, 79.2961, 5.5),
    ("Dhule", "Maharashtra, India", 20.9042, 74.7749, 5.5),
    ("Gondia", "Maharashtra, India", 21.4600, 80.1900, 5.5),
    ("Ichalkaranji", "Maharashtra, India", 16.6912, 74.4605, 5.5),
    ("Jalgaon", "Maharashtra, India", 21.0077, 75.5626, 5.5),
    ("Jalna", "Maharashtra, India", 19.8347, 75.8816, 5.5),
    ("Kolhapur", "Maharashtra, India", 16.7050, 74.2433, 5.5),
    ("Latur", "Maharashtra, India", 18.4088, 76.5604, 5.5),
    ("Malegaon", "Maharashtra, India", 20.5579, 74.5287, 5.5),
    ("Mumbai", "Maharashtra, India", 19.0760, 72.8777, 5.5),
    ("Nagpur", "Maharashtra, India", 21.1458, 79.0882, 5.5),
    ("Nanded", "Maharashtra, India", 19.1383, 77.3210, 5.5),
    ("Nandurbar", "Maharashtra, India", 21.3700, 74.2400, 5.5),
    ("Nashik", "Maharashtra, India", 19.9975, 73.7898, 5.5),
    ("Osmanabad", "Maharashtra, India", 18.1860, 76.0419, 5.5),
    ("Palghar", "Maharashtra, India", 19.6967, 72.7650, 5.5),
    ("Panvel", "Maharashtra, India", 18.9894, 73.1175, 5.5),
    ("Parbhani", "Maharashtra, India", 19.2704, 76.7600, 5.5),
    ("Pimpri-Chinchwad", "Maharashtra, India", 18.6298, 73.7997, 5.5),
    ("Pune", "Maharashtra, India", 18.5204, 73.8567, 5.5),
    ("Sangli", "Maharashtra, India", 16.8524, 74.5815, 5.5),
    ("Satara", "Maharashtra, India", 17.6805, 74.0183, 5.5),
    ("Solapur", "Maharashtra, India", 17.6599, 75.9064, 5.5),
    ("Thane", "Maharashtra, India", 19.2183, 72.9781, 5.5),
    ("Wardha", "Maharashtra, India", 20.7453, 78.6022, 5.5),
    ("Yavatmal", "Maharashtra, India", 20.3899, 78.1307, 5.5),
    ("Imphal", "Manipur, India", 24.8170, 93.9368, 5.5),
    ("Bishnupur", "Manipur, India", 24.6333, 93.7667, 5.5),
    ("Churachandpur", "Manipur, India", 24.3333, 93.6833, 5.5),
    ("Kakching", "Manipur, India", 24.5000, 93.9833, 5.5),
    ("Moirang", "Manipur, India", 24.5006, 93.7770, 5.5),
    ("Senapati", "Manipur, India", 25.2667, 94.0167, 5.5),
    ("Thoubal", "Manipur, India", 24.6388, 93.9964, 5.5),
    ("Ukhrul", "Manipur, India", 25.1087, 94.3617, 5.5),
    ("Shillong", "Meghalaya, India", 25.5788, 91.8933, 5.5),
    ("Tura", "Meghalaya, India", 25.5142, 90.2024, 5.5),
    ("Jowai", "Meghalaya, India", 25.4539, 92.1976, 5.5),
    ("Nongpoh", "Meghalaya, India", 25.9020, 91.8769, 5.5),
    ("Baghmara", "Meghalaya, India", 25.2088, 90.6443, 5.5),
    ("Williamnagar", "Meghalaya, India", 25.4924, 90.6130, 5.5),
    ("Aizawl", "Mizoram, India", 23.7271, 92.7176, 5.5),
    ("Lunglei", "Mizoram, India", 22.8671, 92.7655, 5.5),
    ("Champhai", "Mizoram, India", 23.4560, 93.3282, 5.5),
    ("Kolasib", "Mizoram, India", 24.2239, 92.6787, 5.5),
    ("Serchhip", "Mizoram, India", 23.2988, 92.8460, 5.5),
    ("Saiha", "Mizoram, India", 22.4918, 92.9814, 5.5),
    ("Dimapur", "Nagaland, India", 25.9091, 93.7276, 5.5),
    ("Kohima", "Nagaland, India", 25.6751, 94.1086, 5.5),
    ("Mokokchung", "Nagaland, India", 26.3248, 94.5183, 5.5),
    ("Tuensang", "Nagaland, India", 26.2670, 94.8241, 5.5),
    ("Wokha", "Nagaland, India", 26.0972, 94.2583, 5.5),
    ("Zunheboto", "Nagaland, India", 25.9700, 94.5200, 5.5),
    ("Angul", "Odisha, India", 20.8444, 85.1511, 5.5),
    ("Balangir", "Odisha, India", 20.7042, 83.4903, 5.5),
    ("Balasore", "Odisha, India", 21.4942, 86.9335, 5.5),
    ("Baripada", "Odisha, India", 21.9374, 86.7274, 5.5),
    ("Berhampur", "Odisha, India", 19.3149, 84.7941, 5.5),
    ("Bhadrak", "Odisha, India", 21.0583, 86.4958, 5.5),
    ("Bhubaneswar", "Odisha, India", 20.2961, 85.8245, 5.5),
    ("Cuttack", "Odisha, India", 20.4625, 85.8828, 5.5),
    ("Dhenkanal", "Odisha, India", 20.6709, 85.6017, 5.5),
    ("Jagatsinghpur", "Odisha, India", 20.2549, 86.1706, 5.5),
    ("Jajpur", "Odisha, India", 20.8500, 86.3333, 5.5),
    ("Jharsuguda", "Odisha, India", 21.8554, 84.0062, 5.5),
    ("Kendrapara", "Odisha, India", 20.5000, 86.4200, 5.5),
    ("Keonjhar", "Odisha, India", 21.6289, 85.5810, 5.5),
    ("Koraput", "Odisha, India", 18.8135, 82.7123, 5.5),
    ("Paradeep", "Odisha, India", 20.3167, 86.6167, 5.5),
    ("Phulbani", "Odisha, India", 20.4686, 84.2319, 5.5),
    ("Puri", "Odisha, India", 19.8135, 85.8312, 5.5),
    ("Rayagada", "Odisha, India", 19.1711, 83.4169, 5.5),
    ("Rourkela", "Odisha, India", 22.2604, 84.8536, 5.5),
    ("Sambalpur", "Odisha, India", 21.4669, 83.9812, 5.5),
    ("Sundargarh", "Odisha, India", 22.1167, 84.0333, 5.5),
    ("Amritsar", "Punjab, India", 31.6340, 74.8723, 5.5),
    ("Anandpur Sahib", "Punjab, India", 31.2390, 76.5020, 5.5),
    ("Barnala", "Punjab, India", 30.3819, 75.5468, 5.5),
    ("Batala", "Punjab, India", 31.8186, 75.2028, 5.5),
    ("Bathinda", "Punjab, India", 30.2100, 74.9455, 5.5),
    ("Faridkot", "Punjab, India", 30.6764, 74.7556, 5.5),
    ("Fatehgarh Sahib", "Punjab, India", 30.6456, 76.4043, 5.5),
    ("Fazilka", "Punjab, India", 30.4020, 74.0280, 5.5),
    ("Firozpur", "Punjab, India", 30.9331, 74.6225, 5.5),
    ("Gurdaspur", "Punjab, India", 32.0416, 75.4030, 5.5),
    ("Hoshiarpur", "Punjab, India", 31.5320, 75.9179, 5.5),
    ("Jalandhar", "Punjab, India", 31.3260, 75.5762, 5.5),
    ("Kapurthala", "Punjab, India", 31.3801, 75.3811, 5.5),
    ("Khanna", "Punjab, India", 30.7056, 76.2219, 5.5),
    ("Ludhiana", "Punjab, India", 30.9009, 75.8573, 5.5),
    ("Malerkotla", "Punjab, India", 30.5300, 75.8900, 5.5),
    ("Mansa", "Punjab, India", 29.9880, 75.3920, 5.5),
    ("Moga", "Punjab, India", 30.8172, 75.1717, 5.5),
    ("Mohali", "Punjab, India", 30.7046, 76.7179, 5.5),
    ("Muktsar", "Punjab, India", 30.4762, 74.5166, 5.5),
    ("Nabha", "Punjab, India", 30.3752, 76.1524, 5.5),
    ("Pathankot", "Punjab, India", 32.2643, 75.6421, 5.5),
    ("Patiala", "Punjab, India", 30.3398, 76.3869, 5.5),
    ("Phagwara", "Punjab, India", 31.2240, 75.7708, 5.5),
    ("Rajpura", "Punjab, India", 30.4781, 76.5920, 5.5),
    ("Rupnagar", "Punjab, India", 30.9661, 76.5231, 5.5),
    ("Sangrur", "Punjab, India", 30.2451, 75.8421, 5.5),
    ("Tarn Taran", "Punjab, India", 31.4519, 74.9253, 5.5),
    ("Ajmer", "Rajasthan, India", 26.4499, 74.6399, 5.5),
    ("Alwar", "Rajasthan, India", 27.5530, 76.6346, 5.5),
    ("Banswara", "Rajasthan, India", 23.5461, 74.4349, 5.5),
    ("Baran", "Rajasthan, India", 25.1000, 76.5167, 5.5),
    ("Barmer", "Rajasthan, India", 25.7500, 71.3833, 5.5),
    ("Beawar", "Rajasthan, India", 26.1007, 74.3203, 5.5),
    ("Bharatpur", "Rajasthan, India", 27.2152, 77.5030, 5.5),
    ("Bhilwara", "Rajasthan, India", 25.3471, 74.6408, 5.5),
    ("Bikaner", "Rajasthan, India", 28.0229, 73.3119, 5.5),
    ("Bundi", "Rajasthan, India", 25.4410, 75.6370, 5.5),
    ("Chittorgarh", "Rajasthan, India", 24.8799, 74.6299, 5.5),
    ("Churu", "Rajasthan, India", 28.3042, 74.9672, 5.5),
    ("Dausa", "Rajasthan, India", 26.8932, 76.3375, 5.5),
    ("Dholpur", "Rajasthan, India", 26.7025, 77.8934, 5.5),
    ("Hanumangarh", "Rajasthan, India", 29.5800, 74.3200, 5.5),
    ("Jaipur", "Rajasthan, India", 26.9124, 75.7873, 5.5),
    ("Jaisalmer", "Rajasthan, India", 26.9157, 70.9083, 5.5),
    ("Jalore", "Rajasthan, India", 25.3450, 72.6150, 5.5),
    ("Jhalawar", "Rajasthan, India", 24.5973, 76.1611, 5.5),
    ("Jhunjhunu", "Rajasthan, India", 28.1289, 75.3990, 5.5),
    ("Jodhpur", "Rajasthan, India", 26.2389, 73.0243, 5.5),
    ("Karauli", "Rajasthan, India", 26.4983, 77.0276, 5.5),
    ("Kishangarh", "Rajasthan, India", 26.5901, 74.8530, 5.5),
    ("Kota", "Rajasthan, India", 25.2138, 75.8648, 5.5),
    ("Nagaur", "Rajasthan, India", 27.2020, 73.7339, 5.5),
    ("Pali", "Rajasthan, India", 25.7725, 73.3234, 5.5),
    ("Pratapgarh", "Rajasthan, India", 24.0322, 74.7810, 5.5),
    ("Rajsamand", "Rajasthan, India", 25.0715, 73.8798, 5.5),
    ("Sawai Madhopur", "Rajasthan, India", 26.0230, 76.3441, 5.5),
    ("Sikar", "Rajasthan, India", 27.6094, 75.1399, 5.5),
    ("Sirohi", "Rajasthan, India", 24.8850, 72.8575, 5.5),
    ("Sri Ganganagar", "Rajasthan, India", 29.9038, 73.8772, 5.5),
    ("Tonk", "Rajasthan, India", 26.1664, 75.7885, 5.5),
    ("Udaipur", "Rajasthan, India", 24.5854, 73.7125, 5.5),
    ("Gangtok", "Sikkim, India", 27.3389, 88.6065, 5.5),
    ("Geyzing", "Sikkim, India", 27.2896, 88.2576, 5.5),
    ("Mangan", "Sikkim, India", 27.5167, 88.5333, 5.5),
    ("Namchi", "Sikkim, India", 27.1652, 88.3639, 5.5),
    ("Rangpo", "Sikkim, India", 27.1773, 88.5336, 5.5),
    ("Singtam", "Sikkim, India", 27.2347, 88.5017, 5.5),
    ("Ambur", "Tamil Nadu, India", 12.7904, 78.7166, 5.5),
    ("Arakkonam", "Tamil Nadu, India", 13.0845, 79.6704, 5.5),
    ("Ariyalur", "Tamil Nadu, India", 11.1385, 79.0756, 5.5),
    ("Chengalpattu", "Tamil Nadu, India", 12.6819, 79.9835, 5.5),
    ("Chennai", "Tamil Nadu, India", 13.0827, 80.2707, 5.5),
    ("Coimbatore", "Tamil Nadu, India", 11.0168, 76.9558, 5.5),
    ("Cuddalore", "Tamil Nadu, India", 11.7447, 79.7680, 5.5),
    ("Dharmapuri", "Tamil Nadu, India", 12.1277, 78.1579, 5.5),
    ("Dindigul", "Tamil Nadu, India", 10.3673, 77.9803, 5.5),
    ("Erode", "Tamil Nadu, India", 11.3410, 77.7172, 5.5),
    ("Hosur", "Tamil Nadu, India", 12.7409, 77.8253, 5.5),
    ("Kanchipuram", "Tamil Nadu, India", 12.8342, 79.7036, 5.5),
    ("Kanyakumari", "Tamil Nadu, India", 8.0883, 77.5385, 5.5),
    ("Karur", "Tamil Nadu, India", 10.9601, 78.0766, 5.5),
    ("Krishnagiri", "Tamil Nadu, India", 12.5186, 78.2137, 5.5),
    ("Madurai", "Tamil Nadu, India", 9.9252, 78.1198, 5.5),
    ("Nagapattinam", "Tamil Nadu, India", 10.7656, 79.8428, 5.5),
    ("Nagercoil", "Tamil Nadu, India", 8.1833, 77.4119, 5.5),
    ("Namakkal", "Tamil Nadu, India", 11.2194, 78.1674, 5.5),
    ("Nilgiris (Ooty)", "Tamil Nadu, India", 11.4064, 76.6932, 5.5),
    ("Perambalur", "Tamil Nadu, India", 11.2333, 78.8833, 5.5),
    ("Pollachi", "Tamil Nadu, India", 10.6583, 77.0080, 5.5),
    ("Pudukkottai", "Tamil Nadu, India", 10.3797, 78.8208, 5.5),
    ("Ramanathapuram", "Tamil Nadu, India", 9.3716, 78.8308, 5.5),
    ("Salem", "Tamil Nadu, India", 11.6643, 78.1460, 5.5),
    ("Sivakasi", "Tamil Nadu, India", 9.4493, 77.7974, 5.5),
    ("Thanjavur", "Tamil Nadu, India", 10.7867, 79.1378, 5.5),
    ("Theni", "Tamil Nadu, India", 10.0104, 77.4768, 5.5),
    ("Thoothukudi", "Tamil Nadu, India", 8.7642, 78.1348, 5.5),
    ("Tiruchirappalli", "Tamil Nadu, India", 10.7905, 78.7047, 5.5),
    ("Tirunelveli", "Tamil Nadu, India", 8.7139, 77.7567, 5.5),
    ("Tiruppur", "Tamil Nadu, India", 11.1085, 77.3411, 5.5),
    ("Tiruvallur", "Tamil Nadu, India", 13.1439, 79.9089, 5.5),
    ("Tiruvannamalai", "Tamil Nadu, India", 12.2253, 79.0747, 5.5),
    ("Vellore", "Tamil Nadu, India", 12.9165, 79.1325, 5.5),
    ("Viluppuram", "Tamil Nadu, India", 11.9390, 79.4861, 5.5),
    ("Virudhunagar", "Tamil Nadu, India", 9.5851, 77.9570, 5.5),
    ("Adilabad", "Telangana, India", 19.6641, 78.5320, 5.5),
    ("Bhadradri Kothagudem", "Telangana, India", 17.5511, 80.6176, 5.5),
    ("Hanamkonda", "Telangana, India", 18.0050, 79.5700, 5.5),
    ("Hyderabad", "Telangana, India", 17.3850, 78.4867, 5.5),
    ("Jagtial", "Telangana, India", 18.7907, 78.9120, 5.5),
    ("Karimnagar", "Telangana, India", 18.4386, 79.1288, 5.5),
    ("Khammam", "Telangana, India", 17.2473, 80.1514, 5.5),
    ("Mahabubnagar", "Telangana, India", 16.7375, 77.9838, 5.5),
    ("Medak", "Telangana, India", 18.0453, 78.2600, 5.5),
    ("Nalgonda", "Telangana, India", 17.0544, 79.2671, 5.5),
    ("Nirmal", "Telangana, India", 19.0964, 78.3441, 5.5),
    ("Nizamabad", "Telangana, India", 18.6725, 78.0941, 5.5),
    ("Ramagundam", "Telangana, India", 18.7557, 79.4748, 5.5),
    ("Sangareddy", "Telangana, India", 17.6244, 78.0867, 5.5),
    ("Siddipet", "Telangana, India", 18.1018, 78.8521, 5.5),
    ("Suryapet", "Telangana, India", 17.1405, 79.6200, 5.5),
    ("Warangal", "Telangana, India", 17.9784, 79.5941, 5.5),
    ("Zaheerabad", "Telangana, India", 17.6814, 77.6074, 5.5),
    ("Agartala", "Tripura, India", 23.8315, 91.2868, 5.5),
    ("Belonia", "Tripura, India", 23.2518, 91.4546, 5.5),
    ("Dharmanagar", "Tripura, India", 24.3667, 92.1667, 5.5),
    ("Kailasahar", "Tripura, India", 24.3333, 92.0000, 5.5),
    ("Khowai", "Tripura, India", 24.0670, 91.6030, 5.5),
    ("Udaipur", "Tripura, India", 23.5333, 91.4833, 5.5),
    ("Agra", "Uttar Pradesh, India", 27.1767, 78.0081, 5.5),
    ("Aligarh", "Uttar Pradesh, India", 27.8974, 78.0880, 5.5),
    ("Ambedkar Nagar", "Uttar Pradesh, India", 26.4050, 82.5670, 5.5),
    ("Amethi", "Uttar Pradesh, India", 26.1542, 81.8147, 5.5),
    ("Amroha", "Uttar Pradesh, India", 28.9044, 78.4698, 5.5),
    ("Auraiya", "Uttar Pradesh, India", 26.4652, 79.5092, 5.5),
    ("Ayodhya", "Uttar Pradesh, India", 26.7990, 82.2043, 5.5),
    ("Azamgarh", "Uttar Pradesh, India", 26.0739, 83.1859, 5.5),
    ("Baghpat", "Uttar Pradesh, India", 28.9441, 77.2187, 5.5),
    ("Bahraich", "Uttar Pradesh, India", 27.5743, 81.5940, 5.5),
    ("Ballia", "Uttar Pradesh, India", 25.7580, 84.1480, 5.5),
    ("Balrampur", "Uttar Pradesh, India", 27.4295, 82.1839, 5.5),
    ("Banda", "Uttar Pradesh, India", 25.4753, 80.3351, 5.5),
    ("Barabanki", "Uttar Pradesh, India", 26.9260, 81.1834, 5.5),
    ("Bareilly", "Uttar Pradesh, India", 28.3670, 79.4304, 5.5),
    ("Basti", "Uttar Pradesh, India", 26.8145, 82.7637, 5.5),
    ("Bhadohi", "Uttar Pradesh, India", 25.3956, 82.5703, 5.5),
    ("Bijnor", "Uttar Pradesh, India", 29.3724, 78.1361, 5.5),
    ("Budaun", "Uttar Pradesh, India", 28.0362, 79.1267, 5.5),
    ("Bulandshahr", "Uttar Pradesh, India", 28.4069, 77.8498, 5.5),
    ("Chandauli", "Uttar Pradesh, India", 25.2580, 83.2680, 5.5),
    ("Deoria", "Uttar Pradesh, India", 26.5024, 83.7791, 5.5),
    ("Etah", "Uttar Pradesh, India", 27.5587, 78.6626, 5.5),
    ("Etawah", "Uttar Pradesh, India", 26.7855, 79.0210, 5.5),
    ("Faizabad", "Uttar Pradesh, India", 26.7730, 82.1450, 5.5),
    ("Farrukhabad", "Uttar Pradesh, India", 27.3913, 79.5793, 5.5),
    ("Fatehpur", "Uttar Pradesh, India", 25.9304, 80.8139, 5.5),
    ("Firozabad", "Uttar Pradesh, India", 27.1592, 78.3957, 5.5),
    ("Gautam Buddha Nagar (Noida)", "Uttar Pradesh, India", 28.5355, 77.3910, 5.5),
    ("Ghaziabad", "Uttar Pradesh, India", 28.6692, 77.4538, 5.5),
    ("Ghazipur", "Uttar Pradesh, India", 25.5840, 83.5770, 5.5),
    ("Gonda", "Uttar Pradesh, India", 27.1330, 81.9619, 5.5),
    ("Gorakhpur", "Uttar Pradesh, India", 26.7606, 83.3732, 5.5),
    ("Hamirpur", "Uttar Pradesh, India", 25.9546, 80.1480, 5.5),
    ("Hapur", "Uttar Pradesh, India", 28.7306, 77.7759, 5.5),
    ("Hardoi", "Uttar Pradesh, India", 27.3949, 80.1311, 5.5),
    ("Hathras", "Uttar Pradesh, India", 27.5955, 78.0520, 5.5),
    ("Jalaun", "Uttar Pradesh, India", 26.1451, 79.3367, 5.5),
    ("Jaunpur", "Uttar Pradesh, India", 25.7464, 82.6837, 5.5),
    ("Jhansi", "Uttar Pradesh, India", 25.4484, 78.5685, 5.5),
    ("Kannauj", "Uttar Pradesh, India", 27.0552, 79.9181, 5.5),
    ("Kanpur", "Uttar Pradesh, India", 26.4499, 80.3319, 5.5),
    ("Kasganj", "Uttar Pradesh, India", 27.8129, 78.6498, 5.5),
    ("Kaushambi", "Uttar Pradesh, India", 25.5308, 81.3786, 5.5),
    ("Kushinagar", "Uttar Pradesh, India", 26.7408, 83.8881, 5.5),
    ("Lakhimpur Kheri", "Uttar Pradesh, India", 27.9462, 80.7787, 5.5),
    ("Lalitpur", "Uttar Pradesh, India", 24.6909, 78.4186, 5.5),
    ("Lucknow", "Uttar Pradesh, India", 26.8467, 80.9462, 5.5),
    ("Maharajganj", "Uttar Pradesh, India", 27.1450, 83.5620, 5.5),
    ("Mahoba", "Uttar Pradesh, India", 25.2921, 79.8724, 5.5),
    ("Mainpuri", "Uttar Pradesh, India", 27.2285, 79.0288, 5.5),
    ("Mathura", "Uttar Pradesh, India", 27.4924, 77.6737, 5.5),
    ("Mau", "Uttar Pradesh, India", 25.9417, 83.5611, 5.5),
    ("Meerut", "Uttar Pradesh, India", 28.9845, 77.7064, 5.5),
    ("Mirzapur", "Uttar Pradesh, India", 25.1460, 82.5690, 5.5),
    ("Moradabad", "Uttar Pradesh, India", 28.8386, 78.7733, 5.5),
    ("Muzaffarnagar", "Uttar Pradesh, India", 29.4727, 77.7085, 5.5),
    ("Pilibhit", "Uttar Pradesh, India", 28.6312, 79.8044, 5.5),
    ("Pratapgarh", "Uttar Pradesh, India", 25.8979, 81.9450, 5.5),
    ("Prayagraj", "Uttar Pradesh, India", 25.4358, 81.8463, 5.5),
    ("Raebareli", "Uttar Pradesh, India", 26.2309, 81.2335, 5.5),
    ("Rampur", "Uttar Pradesh, India", 28.7983, 79.0220, 5.5),
    ("Saharanpur", "Uttar Pradesh, India", 29.9680, 77.5552, 5.5),
    ("Sambhal", "Uttar Pradesh, India", 28.5830, 78.5696, 5.5),
    ("Sant Kabir Nagar", "Uttar Pradesh, India", 26.7900, 83.0700, 5.5),
    ("Shahjahanpur", "Uttar Pradesh, India", 27.8804, 79.9090, 5.5),
    ("Shamli", "Uttar Pradesh, India", 29.4502, 77.3178, 5.5),
    ("Shravasti", "Uttar Pradesh, India", 27.5075, 82.0435, 5.5),
    ("Siddharthnagar", "Uttar Pradesh, India", 27.2570, 83.0730, 5.5),
    ("Sitapur", "Uttar Pradesh, India", 27.5619, 80.6827, 5.5),
    ("Sonbhadra", "Uttar Pradesh, India", 24.6850, 83.0680, 5.5),
    ("Sultanpur", "Uttar Pradesh, India", 26.2648, 82.0727, 5.5),
    ("Unnao", "Uttar Pradesh, India", 26.5471, 80.4878, 5.5),
    ("Varanasi", "Uttar Pradesh, India", 25.3176, 82.9739, 5.5),
    ("Almora", "Uttarakhand, India", 29.5971, 79.6591, 5.5),
    ("Bageshwar", "Uttarakhand, India", 29.8370, 79.7710, 5.5),
    ("Chamoli", "Uttarakhand, India", 30.4030, 79.3230, 5.5),
    ("Champawat", "Uttarakhand, India", 29.3360, 80.0910, 5.5),
    ("Dehradun", "Uttarakhand, India", 30.3165, 78.0322, 5.5),
    ("Haldwani", "Uttarakhand, India", 29.2183, 79.5120, 5.5),
    ("Haridwar", "Uttarakhand, India", 29.9457, 78.1642, 5.5),
    ("Kashipur", "Uttarakhand, India", 29.2145, 78.9569, 5.5),
    ("Kotdwar", "Uttarakhand, India", 29.7465, 78.5225, 5.5),
    ("Nainital", "Uttarakhand, India", 29.3803, 79.4636, 5.5),
    ("Pauri", "Uttarakhand, India", 30.1524, 78.7808, 5.5),
    ("Pithoragarh", "Uttarakhand, India", 29.5829, 80.2182, 5.5),
    ("Rishikesh", "Uttarakhand, India", 30.0869, 78.2676, 5.5),
    ("Rudrapur", "Uttarakhand, India", 28.9875, 79.4141, 5.5),
    ("Tehri", "Uttarakhand, India", 30.3785, 78.4800, 5.5),
    ("Udham Singh Nagar", "Uttarakhand, India", 28.9750, 79.3950, 5.5),
    ("Uttarkashi", "Uttarakhand, India", 30.7290, 78.4430, 5.5),
    ("Alipurduar", "West Bengal, India", 26.4837, 89.5229, 5.5),
    ("Asansol", "West Bengal, India", 23.6739, 86.9524, 5.5),
    ("Bally", "West Bengal, India", 22.6500, 88.3400, 5.5),
    ("Balurghat", "West Bengal, India", 25.2167, 88.7833, 5.5),
    ("Bangaon", "West Bengal, India", 23.0450, 88.8300, 5.5),
    ("Bankura", "West Bengal, India", 23.2324, 87.0784, 5.5),
    ("Baranagar", "West Bengal, India", 22.6400, 88.3700, 5.5),
    ("Barasat", "West Bengal, India", 22.7215, 88.4810, 5.5),
    ("Barrackpore", "West Bengal, India", 22.7600, 88.3700, 5.5),
    ("Basirhat", "West Bengal, India", 22.6574, 88.8672, 5.5),
    ("Bardhaman", "West Bengal, India", 23.2324, 87.8615, 5.5),
    ("Berhampore", "West Bengal, India", 24.1047, 88.2516, 5.5),
    ("Bhatpara", "West Bengal, India", 22.8664, 88.4011, 5.5),
    ("Bidhannagar", "West Bengal, India", 22.5867, 88.4170, 5.5),
    ("Birbhum", "West Bengal, India", 23.8400, 87.6200, 5.5),
    ("Bolpur", "West Bengal, India", 23.6693, 87.6820, 5.5),
    ("Chandannagar", "West Bengal, India", 22.8667, 88.3667, 5.5),
    ("Cooch Behar", "West Bengal, India", 26.3240, 89.4482, 5.5),
    ("Darjeeling", "West Bengal, India", 27.0360, 88.2627, 5.5),
    ("Diamond Harbour", "West Bengal, India", 22.1936, 88.1902, 5.5),
    ("Dum Dum", "West Bengal, India", 22.6400, 88.4200, 5.5),
    ("Durgapur", "West Bengal, India", 23.5204, 87.3119, 5.5),
    ("English Bazar (Malda)", "West Bengal, India", 25.0108, 88.1411, 5.5),
    ("Habra", "West Bengal, India", 22.8420, 88.6561, 5.5),
    ("Haldia", "West Bengal, India", 22.0667, 88.0698, 5.5),
    ("Hooghly", "West Bengal, India", 22.9000, 88.3900, 5.5),
    ("Howrah", "West Bengal, India", 22.5958, 88.2636, 5.5),
    ("Islampur", "West Bengal, India", 26.2654, 88.2015, 5.5),
    ("Jalpaiguri", "West Bengal, India", 26.5435, 88.7205, 5.5),
    ("Jhargram", "West Bengal, India", 22.4500, 86.9800, 5.5),
    ("Kalimpong", "West Bengal, India", 27.0600, 88.4700, 5.5),
    ("Kalyani", "West Bengal, India", 22.9750, 88.4344, 5.5),
    ("Kharagpur", "West Bengal, India", 22.3460, 87.2319, 5.5),
    ("Kolkata", "West Bengal, India", 22.5726, 88.3639, 5.5),
    ("Krishnanagar", "West Bengal, India", 23.4000, 88.5000, 5.5),
    ("Medinipur", "West Bengal, India", 22.4250, 87.3199, 5.5),
    ("Murshidabad", "West Bengal, India", 24.1800, 88.2700, 5.5),
    ("Nabadwip", "West Bengal, India", 23.4000, 88.3700, 5.5),
    ("North Dum Dum", "West Bengal, India", 22.6333, 88.4220, 5.5),
    ("Purulia", "West Bengal, India", 23.3300, 86.3600, 5.5),
    ("Raiganj", "West Bengal, India", 25.6200, 88.1200, 5.5),
    ("Ranaghat", "West Bengal, India", 23.1765, 88.5667, 5.5),
    ("Serampore", "West Bengal, India", 22.7528, 88.3400, 5.5),
    ("Siliguri", "West Bengal, India", 26.7271, 88.3953, 5.5),
    ("Tamluk", "West Bengal, India", 22.3000, 87.9200, 5.5),
    ("Kavaratti", "Lakshadweep, India", 10.5667, 72.6417, 5.5),
    ("Silvassa", "Dadra and Nagar Haveli and Daman and Diu, India", 20.2763, 73.0083, 5.5),
    ("Daman", "Dadra and Nagar Haveli and Daman and Diu, India", 20.3974, 72.8328, 5.5),
    ("Diu", "Dadra and Nagar Haveli and Daman and Diu, India", 20.7141, 70.9876, 5.5),
    ("New Delhi", "Delhi, India", 28.6139, 77.2090, 5.5),
    ("Delhi", "Delhi, India", 28.7041, 77.1025, 5.5),
    ("Puducherry", "Puducherry, India", 11.9416, 79.8083, 5.5),
    ("Karaikal", "Puducherry, India", 10.9254, 79.8380, 5.5),
    ("Mahe", "Puducherry, India", 11.7000, 75.5333, 5.5),
    ("Yanam", "Puducherry, India", 16.7333, 82.2167, 5.5),
    ("Greater Noida", "Uttar Pradesh, India", 28.4744, 77.5040, 5.5),
    ("Jewar", "Uttar Pradesh, India", 28.1235, 77.5553, 5.5),
    ("Modinagar", "Uttar Pradesh, India", 28.8310, 77.5770, 5.5),
    ("Dadri", "Uttar Pradesh, India", 28.5520, 77.5530, 5.5),
    ("Sikandrabad", "Uttar Pradesh, India", 28.4500, 77.7000, 5.5),
    ("Khurja", "Uttar Pradesh, India", 28.2530, 77.8550, 5.5),
    ("Vrindavan", "Uttar Pradesh, India", 27.5800, 77.7000, 5.5),
    ("Chitrakoot", "Uttar Pradesh, India", 25.2000, 80.9000, 5.5),
    ("Mughalsarai", "Uttar Pradesh, India", 25.2800, 83.1200, 5.5),
    ("Renukoot", "Uttar Pradesh, India", 24.2000, 83.0400, 5.5),
    ("Obra", "Uttar Pradesh, India", 24.4200, 82.9800, 5.5),
    ("Shikohabad", "Uttar Pradesh, India", 27.1000, 78.6000, 5.5),
    ("Tundla", "Uttar Pradesh, India", 27.2100, 78.2800, 5.5),
    ("Sikandra Rao", "Uttar Pradesh, India", 27.6900, 78.3800, 5.5),
    ("Gola Gokarannath", "Uttar Pradesh, India", 28.0800, 80.4700, 5.5),
    ("Palia Kalan", "Uttar Pradesh, India", 28.4300, 80.5800, 5.5),
    ("Tilhar", "Uttar Pradesh, India", 27.9700, 79.7400, 5.5),
    ("Najibabad", "Uttar Pradesh, India", 29.6100, 78.3400, 5.5),
    ("Nagina", "Uttar Pradesh, India", 29.4400, 78.4300, 5.5),
    ("Chandausi", "Uttar Pradesh, India", 28.4500, 78.7800, 5.5),
    ("Gangoh", "Uttar Pradesh, India", 29.7800, 77.2600, 5.5),
    ("Behat", "Uttar Pradesh, India", 30.1700, 77.6100, 5.5),
    ("Mawana", "Uttar Pradesh, India", 29.1000, 77.9200, 5.5),
    ("Sardhana", "Uttar Pradesh, India", 29.1500, 77.6200, 5.5),
    ("Kairana", "Uttar Pradesh, India", 29.4000, 77.2000, 5.5),
    ("Deoband", "Uttar Pradesh, India", 29.6900, 77.6800, 5.5),
    ("Robertsganj", "Uttar Pradesh, India", 24.6900, 83.0700, 5.5),
    ("Gauriganj", "Uttar Pradesh, India", 26.2000, 81.7000, 5.5),
    ("Loni", "Uttar Pradesh, India", 28.7500, 77.2900, 5.5),
    ("Shahabad", "Uttar Pradesh, India", 27.6500, 79.9500, 5.5),
    ("Pukhrayan", "Uttar Pradesh, India", 26.2200, 79.8400, 5.5),
    ("Bindki", "Uttar Pradesh, India", 25.6100, 80.5800, 5.5),
    ("Rasra", "Uttar Pradesh, India", 25.8600, 83.8600, 5.5),
    ("Padrauna", "Uttar Pradesh, India", 26.9000, 83.9800, 5.5),
    ("Colonelganj", "Uttar Pradesh, India", 27.1300, 81.6900, 5.5),
    ("Nautanwa", "Uttar Pradesh, India", 27.4300, 83.4200, 5.5),
    ("Laharpur", "Uttar Pradesh, India", 27.7100, 80.9000, 5.5),
    ("Bisalpur", "Uttar Pradesh, India", 28.3000, 79.8000, 5.5),
    ("Faridpur", "Uttar Pradesh, India", 28.2100, 79.5400, 5.5),
    ("Aonla", "Uttar Pradesh, India", 28.2700, 79.1500, 5.5),
    ("Bilsi", "Uttar Pradesh, India", 28.1300, 78.9200, 5.5),
    ("Dataganj", "Uttar Pradesh, India", 28.0200, 79.4000, 5.5),
    ("Anupshahr", "Uttar Pradesh, India", 28.3600, 78.2700, 5.5),
    ("Dibai", "Uttar Pradesh, India", 28.2100, 78.2600, 5.5),
    ("Siana", "Uttar Pradesh, India", 28.6300, 78.0600, 5.5),
    ("Pahasu", "Uttar Pradesh, India", 28.1800, 78.0700, 5.5),
    ("Jahangirabad", "Uttar Pradesh, India", 28.4000, 77.9800, 5.5),
    ("Anupgarh", "Rajasthan, India", 29.1900, 73.2100, 5.5),
    ("Neem Ka Thana", "Rajasthan, India", 27.7400, 75.7900, 5.5),
    ("Kotputli", "Rajasthan, India", 27.7000, 76.2000, 5.5),
    ("Didwana", "Rajasthan, India", 27.4000, 74.5700, 5.5),
    ("Ladnun", "Rajasthan, India", 27.6500, 74.4000, 5.5),
    ("Makrana", "Rajasthan, India", 27.0500, 74.7200, 5.5),
    ("Kuchaman City", "Rajasthan, India", 27.1500, 74.8500, 5.5),
    ("Phalodi", "Rajasthan, India", 27.1300, 72.3700, 5.5),
    ("Pokaran", "Rajasthan, India", 26.9200, 71.9200, 5.5),
    ("Balotra", "Rajasthan, India", 25.8300, 72.2400, 5.5),
    ("Jaitaran", "Rajasthan, India", 26.2100, 73.9400, 5.5),
    ("Sojat", "Rajasthan, India", 25.9200, 73.6700, 5.5),
    ("Falna", "Rajasthan, India", 25.2300, 73.2400, 5.5),
    ("Abu Road", "Rajasthan, India", 24.4800, 72.7800, 5.5),
    ("Mount Abu", "Rajasthan, India", 24.5900, 72.7100, 5.5),
    ("Nathdwara", "Rajasthan, India", 24.9300, 73.8200, 5.5),
    ("Kankroli", "Rajasthan, India", 25.0700, 73.8800, 5.5),
    ("Kapasan", "Rajasthan, India", 24.8800, 74.7000, 5.5),
    ("Nimbahera", "Rajasthan, India", 24.6200, 74.6800, 5.5),
    ("Rawatbhata", "Rajasthan, India", 24.9300, 75.5800, 5.5),
    ("Ramganj Mandi", "Rajasthan, India", 24.6500, 75.9400, 5.5),
    ("Anta", "Rajasthan, India", 25.1500, 76.3000, 5.5),
    ("Jhalrapatan", "Rajasthan, India", 24.5500, 76.1700, 5.5),
    ("Gangapur City", "Rajasthan, India", 26.4700, 76.7200, 5.5),
    ("Hindaun City", "Rajasthan, India", 26.7300, 77.0400, 5.5),
    ("Bayana", "Rajasthan, India", 26.9000, 77.2900, 5.5),
    ("Deeg", "Rajasthan, India", 27.4700, 77.3200, 5.5),
    ("Kaman", "Rajasthan, India", 27.6500, 77.2700, 5.5),
    ("Nadbai", "Rajasthan, India", 27.2200, 77.1900, 5.5),
    ("Laxmangarh", "Rajasthan, India", 27.8200, 75.0300, 5.5),
    ("Fatehpur", "Rajasthan, India", 27.9900, 74.9600, 5.5),
    ("Ratangarh", "Rajasthan, India", 28.0800, 74.6200, 5.5),
    ("Sujangarh", "Rajasthan, India", 27.7000, 74.4700, 5.5),
    ("Nohar", "Rajasthan, India", 29.1800, 74.7700, 5.5),
    ("Rawatsar", "Rajasthan, India", 29.2700, 74.4000, 5.5),
    ("Pilibanga", "Rajasthan, India", 29.5200, 74.0800, 5.5),
    ("Raisinghnagar", "Rajasthan, India", 29.5300, 73.4500, 5.5),
    ("Sadulshahar", "Rajasthan, India", 29.9100, 73.8700, 5.5),
    ("Suratgarh", "Rajasthan, India", 29.3200, 73.9000, 5.5),
    ("Bhadra", "Rajasthan, India", 29.1000, 75.1700, 5.5),
    ("Taranagar", "Rajasthan, India", 28.6700, 75.0300, 5.5),
    ("Rajgarh", "Rajasthan, India", 28.6300, 75.3800, 5.5),
    ("Sardarshahar", "Rajasthan, India", 28.4400, 74.4900, 5.5),
    ("Nokha", "Rajasthan, India", 27.5600, 73.4700, 5.5),
    ("Deshnoke", "Rajasthan, India", 27.8000, 73.3400, 5.5),
    ("Kolayat", "Rajasthan, India", 27.8500, 72.9600, 5.5),
    ("Lunkaransar", "Rajasthan, India", 28.8400, 73.2800, 5.5),
    ("Osian", "Rajasthan, India", 26.7200, 72.9100, 5.5),
    ("Bilara", "Rajasthan, India", 26.1800, 73.7100, 5.5),
    ("Pipar City", "Rajasthan, India", 26.3800, 73.5500, 5.5),
    ("Shergarh", "Rajasthan, India", 26.3200, 72.3000, 5.5),
    ("Bhinmal", "Rajasthan, India", 24.9900, 72.2700, 5.5),
    ("Sanchore", "Rajasthan, India", 24.7600, 71.7700, 5.5),
    ("Raniwara", "Rajasthan, India", 24.7500, 72.2200, 5.5),
    ("Pindwara", "Rajasthan, India", 24.7900, 73.0500, 5.5),
    ("Reodar", "Rajasthan, India", 24.8500, 72.8500, 5.5),
    ("Dungarpur", "Rajasthan, India", 23.8400, 73.7100, 5.5),
    ("Sagwara", "Rajasthan, India", 23.6700, 74.0000, 5.5),
    ("Aspur", "Rajasthan, India", 23.9000, 74.1500, 5.5),
    ("Kushalgarh", "Rajasthan, India", 23.2000, 74.4500, 5.5),
    ("Bari Sadri", "Rajasthan, India", 24.4200, 74.4700, 5.5),
    ("Begun", "Rajasthan, India", 24.9800, 75.0000, 5.5),
    ("Amet", "Rajasthan, India", 25.3000, 73.9300, 5.5),
    ("Bhim", "Rajasthan, India", 25.2000, 73.9700, 5.5),
    ("Devgarh", "Rajasthan, India", 25.5200, 73.9000, 5.5),
    ("Kelwa", "Rajasthan, India", 25.1200, 73.8200, 5.5),
    ("Salumber", "Rajasthan, India", 24.0800, 74.0500, 5.5),
    ("Vallabhnagar", "Rajasthan, India", 24.6700, 74.0000, 5.5),
    ("Pratapgarh Road", "Rajasthan, India", 24.0300, 74.7800, 5.5),
    ("Chhoti Sadri", "Rajasthan, India", 24.3800, 74.7000, 5.5),
    ("Arnod", "Rajasthan, India", 24.8700, 74.9900, 5.5),
    ("Bassi", "Rajasthan, India", 26.8400, 76.0500, 5.5),
    ("Chaksu", "Rajasthan, India", 26.6100, 75.9500, 5.5),
    ("Dudu", "Rajasthan, India", 26.8900, 75.7200, 5.5),
    ("Jobner", "Rajasthan, India", 26.9700, 75.3800, 5.5),
    ("Phulera", "Rajasthan, India", 26.8700, 75.2400, 5.5),
    ("Sambhar", "Rajasthan, India", 26.9100, 75.2000, 5.5),
    ("Shahpura", "Rajasthan, India", 27.3900, 75.9600, 5.5),
    ("Viratnagar", "Rajasthan, India", 27.4400, 76.1800, 5.5),
    ("Neemrana", "Rajasthan, India", 27.9900, 76.3900, 5.5),
    ("Bansur", "Rajasthan, India", 27.6800, 76.3500, 5.5),
    ("Behror", "Rajasthan, India", 27.8900, 76.2800, 5.5),
    ("Tijara", "Rajasthan, India", 27.9300, 76.8500, 5.5),
    ("Khairthal", "Rajasthan, India", 27.8000, 76.6500, 5.5),
    ("Rajakhera", "Rajasthan, India", 26.9000, 78.1700, 5.5),
    ("Baswa", "Rajasthan, India", 27.1500, 76.5800, 5.5),
    ("Bandikui", "Rajasthan, India", 27.0500, 76.5700, 5.5),
    ("Lalsot", "Rajasthan, India", 26.5600, 76.3300, 5.5),
    ("Sawai", "Rajasthan, India", 26.0200, 76.3400, 5.5),
    ("Uniara", "Rajasthan, India", 26.1500, 75.2200, 5.5),
    ("Malpura", "Rajasthan, India", 26.2900, 75.3800, 5.5),
    ("Todaraisingh", "Rajasthan, India", 26.0300, 75.4800, 5.5),
    ("Niwai", "Rajasthan, India", 26.3600, 75.9200, 5.5),
    ("Keshoraipatan", "Rajasthan, India", 25.3000, 75.9300, 5.5),
    ("Lakheri", "Rajasthan, India", 25.6700, 76.1700, 5.5),
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

    # ---- Chara Kāraka (8-body scheme: Su,Mo,Ma,Me,Jp,Ve,Sa,Ra — Rāhu reversed, Ketu excluded)
    body_by_key = {b["key"]: b for b in bodies}
    karaka_degrees = {}
    for k in ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa"]:
        karaka_degrees[k] = body_by_key[k]["inSign"]
    karaka_degrees["Ra"] = 30.0 - body_by_key["Ra"]["inSign"]
    karaka_map = chara_karaka(karaka_degrees)
    for b in bodies:
        b["karaka"] = karaka_map.get(b["key"])

    # ---- Combustion (within classical orb of the Sun, tropical longitudes)
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

    # JS getDay(): Sunday=0..Saturday=6.  Python isoweekday(): Monday=1..Sunday=7.
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
    """Vimśottarī antardaśā (sub-periods) within one mahādaśā.
    Sequence starts at the mahādaśā's own lord and cycles through all 9 in order;
    each sub-period's length is proportional to its lord's full dasha-years out of 120."""
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
    """Vimśottarī pratyantardaśā (sub-sub-periods) within one antardaśā.
    Same nested-cycle rule as the mahādaśā -> antardaśā step, one level deeper:
    sequence starts at the antardaśā's own lord and cycles through all 9 lords,
    each slice proportional to its lord's full dasha-years out of 120."""
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
    """UTC 'now' shifted into the city's local wall-clock time (naive datetime)."""
    return datetime.utcnow() + timedelta(hours=tz)


# ============================================================
# COLORS  (butterscotch-tinted background)
# ============================================================

C = {
    "bg": "#F6DFAE", "panel": "#FFFFFF", "panelSoft": "#FBEFD6", "line": "#E7D3A4",
    "gold": "#B8842E", "ivory": "#3A2E1F", "muted": "#7A6F5C", "sindoor": "#C4462B",
    "moon": "#3A5B8C",
}

HOUSE_CENTERS = [
    (200, 100), (100, 50), (50, 100), (102, 200), (50, 300), (100, 350),
    (200, 297), (300, 350), (350, 300), (298, 200), (350, 100), (300, 50),
]


def build_svg_chart(birth_bodies, transit_bodies, asc_sign: int) -> str:
    """Builds the same North-Indian style diamond chart as the React <CombinedChart>."""
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
        '<svg viewBox="0 0 400 400" width="440" height="440" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="cbg" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDF7" /><stop offset="100%" stop-color="#F3EAD3" />'
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
    """Point on a circle at radius r, angle measured clockwise from straight up (12 o'clock)."""
    rad = clockwise_deg * D2R
    return cx + r * math.sin(rad), cy - r * math.cos(rad)


def build_circular_svg_chart(birth_bodies, transit_bodies, asc_sign: int, asc_deg_in_sign: float) -> str:
    """Circular (rāśi-wheel) chart: signs fixed to the zodiac (Aries at top, running
    counter-clockwise), an outer nakṣatra ring, dashed house spokes, and an Oṃ at the
    centre — in the style of the reference screenshot."""
    cx, cy = 300, 300
    R_outer = 280
    R_nak_out, R_nak_in = 272, 240
    R_sign_out, R_sign_in = 240, 205
    R_house_num = 185
    R_body_ring_out, R_body_ring_in = 205, 60

    def sign_center_angle(sign_idx):
        return -(sign_idx * 30) % 360

    def nak_center_angle(nak_idx):
        return -(nak_idx * (360 / 27)) % 360

    parts = [
        f'<svg viewBox="0 0 {2*cx} {2*cy}" width="480" height="480" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="cwheel" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDF7" /><stop offset="100%" stop-color="#F6EBCF" />'
        '</radialGradient></defs>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_outer}" fill="url(#cwheel)" stroke="{C["gold"]}" stroke-width="2"/>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_nak_in}" fill="none" stroke="{C["line"]}" stroke-width="1"/>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_sign_in}" fill="none" stroke="{C["gold"]}" stroke-width="1.2"/>',
    ]

    # nakshatra ring: 27 boundary ticks + abbreviation labels
    for n in range(27):
        boundary = (-(n * (360 / 27)) + (360 / 54)) % 360
        x1, y1 = _wheel_point(cx, cy, R_nak_in, boundary)
        x2, y2 = _wheel_point(cx, cy, R_nak_out, boundary)
        parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                      f'stroke="{C["line"]}" stroke-width="1"/>')
        lx, ly = _wheel_point(cx, cy, (R_nak_out + R_nak_in) / 2, nak_center_angle(n))
        parts.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="9" fill="{C["muted"]}" font-family="monospace">{n+1} {NAK_ABBR[n]}</text>')

    # sign ring: 12 boundary lines + sign abbreviation
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

    # dashed spokes from centre to each sign boundary, and house numbers
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

    # ascendant marker (purple tick + "As" at its exact degree)
    asc_angle = sign_center_angle(asc_sign) - (asc_deg_in_sign - 15) * (30 / 30)
    asc_angle = (-(asc_sign * 30 + asc_deg_in_sign) + 15) % 360
    ax1, ay1 = _wheel_point(cx, cy, R_sign_in - 25, asc_angle)
    ax2, ay2 = _wheel_point(cx, cy, R_sign_out, asc_angle)
    parts.append(f'<line x1="{ax1:.1f}" y1="{ay1:.1f}" x2="{ax2:.1f}" y2="{ay2:.1f}" '
                 f'stroke="{C["moon"]}" stroke-width="2.5"/>')
    tx, ty = _wheel_point(cx, cy, R_body_ring_out + 14, asc_angle)
    parts.append(f'<text x="{tx:.1f}" y="{ty:.1f}" text-anchor="middle" dominant-baseline="middle" '
                 f'font-size="13" font-weight="700" fill="{C["moon"]}" '
                 f'font-family="Georgia, serif">As</text>')

    # planets — birth (ivory) in the outer part of the body ring, transits (red) closer in
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

    # centre Oṃ symbol
    parts.append(f'<circle cx="{cx}" cy="{cy}" r="30" fill="{C["panel"]}" stroke="{C["gold"]}" stroke-width="1.5"/>')
    parts.append(f'<text x="{cx}" y="{cy}" text-anchor="middle" dominant-baseline="middle" '
                 f'font-size="30" fill="{C["gold"]}">ॐ</text>')

    parts.append("</svg>")
    return "".join(parts)


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
        text-align: left; color: {C["gold"]}; font-weight: 700; text-decoration: underline;
        padding: 6px 10px; border-bottom: 2px solid {C["line"]}; white-space: nowrap;
    }}
    .gtable td {{ padding: 7px 10px; border-bottom: 1px solid {C["line"]}; white-space: nowrap; }}
    .gtable tr:nth-child(even) {{ background: {C["panelSoft"]}; }}
    .gtable .lord {{ color: {C["sindoor"]}; font-weight: 600; }}
    .gtable .body-key {{ font-weight: 700; }}
    </style>
    """,
    unsafe_allow_html=True,
)

st.markdown(
    f'<h1 style="color:{C["gold"]}; font-family:Georgia, serif; letter-spacing:0.06em;">Kuṇḍalī</h1>'
    f'<p class="kmuted" style="margin-top:-10px; font-size:18px;">Vedic birth-chart engine · Lahiri ayanamsa · Python build</p>',
    unsafe_allow_html=True,
)

# ---- Birth details form -------------------------------------------------
st.markdown('<div class="kcard"><h4>Birth details</h4>', unsafe_allow_html=True)

col1, col2, col3, col4, col5 = st.columns([1.2, 1.6, 1, 1, 0.8])

with col1:
    name = st.text_input("Name", value="", placeholder="Name of chart")

with col2:
    city_query = st.text_input("Birth place (city)", value="Bathinda")
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
    dob = st.date_input(
        "Date of birth", value=date(2026, 7, 16),
        min_value=date(1900, 1, 1), max_value=date(2100, 12, 31),
    )

with col4:
    tob = st.time_input("Time (24h, local)", value=dtime(12, 16))

with col5:
    st.markdown("<br>", unsafe_allow_html=True)
    cast = st.button("Cast chart", use_container_width=True)

st.markdown("</div>", unsafe_allow_html=True)

# Keep last-cast form in session_state so the chart persists across reruns
if "form" not in st.session_state or cast:
    st.session_state["form"] = {
        "name": name, "dob": dob, "tob": tob, "city": city,
    }

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

# ---- Row 1: Combined chart + Nakṣatra panel (right beside the chart) ------
c1, c2 = st.columns([2, 1])

with c1:
    chart_style = st.radio(
        "Chart style", ["North Indian (diamond)", "Circular (rāśi wheel)"],
        horizontal=True, label_visibility="collapsed",
    )
    st.markdown(
        f'<div class="kcard"><h4>Janma Kuṇḍalī + Gochara '
        f'<span class="kmuted" style="text-transform:none;letter-spacing:normal;font-size:13px;">'
        f'&nbsp;&nbsp;{form["city"][0]} · transits {transit_label}</span></h4>',
        unsafe_allow_html=True,
    )
    if chart_style.startswith("Circular"):
        svg = build_circular_svg_chart(birth_chart["bodies"], transit_chart["bodies"],
                                        b_asc["sign"], b_asc["inSign"])
        height = 500
    else:
        svg = build_svg_chart(birth_chart["bodies"], transit_chart["bodies"], b_asc["sign"])
        height = 470
    st.components.v1.html(
        f'<div style="display:flex;justify-content:center;">{svg}</div>', height=height
    )
    st.markdown(
        f"""
        <div style="display:flex;gap:20px;justify-content:center;font-size:14px;flex-wrap:wrap;">
            <span><span style="color:{C['ivory']}">●</span> Birth · {form['dob'].strftime('%Y-%m-%d')} {form['tob'].strftime('%H:%M')}</span>
            <span class="ksindoor"><span style="color:{C['sindoor']}">●</span> Transit · now</span>
            <span class="kmuted">℞ retrograde</span>
        </div>
        <p class="kmuted" style="text-align:center;font-size:14px;margin-top:8px;">
            {(form['name'] + ' · ') if form['name'] else ''}Lagna {SIGNS[b_asc['sign']]} {fmt_deg(b_asc['inSign'])}
            · Moon in {SIGNS[b_moon['sign']]} · houses fixed to birth lagna
        </p>
        </div>
        """,
        unsafe_allow_html=True,
    )

with c2:
    st.markdown('<div class="kcard"><h4>Nakṣatra · birth</h4>', unsafe_allow_html=True)
    nak_rows = "".join(
        f'<div class="krow"><span class="kmuted body-key">{b["key"]}</span>'
        f'<span style="text-align:right;">{NAKSHATRAS[b["nakIdx"]]}'
        f'<span class="kmuted">({b["nakIdx"]+1})</span> '
        f'<span class="lord ksindoor">{DASHA_LORD_SHORT[b["nakIdx"] % 9]}</span>'
        f'<br><span class="kmuted" style="font-size:13px;">pada {b["pada"]}</span></span></div>'
        for b in birth_chart["bodies"]
    )
    st.markdown(nak_rows, unsafe_allow_html=True)
    st.markdown(
        f'<p class="ksindoor" style="font-size:14px;margin-top:10px;">'
        f'Moon Nakṣatra now: {NAKSHATRAS[tp["nakIdx"]]}</p></div>',
        unsafe_allow_html=True,
    )

# ---- Row 2: Vimśottarī Mahādaśā (+ Antardaśā + Pratyantardaśā) beside Pañcāṅga -------------
c3, c4 = st.columns([1, 1])

with c3:
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
                # ---- Pratyantardaśā: 3rd-level sub-sub-periods within this antardaśā.
                # Streamlit doesn't support nested st.expander widgets, so this level
                # renders as an always-visible, further-indented mini-list right under
                # its parent antardaśā row.
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

with c4:
    rows = [
        ("Vāra", birth_chart["panchanga"]["vara"]),
        ("Tithi", f"{birth_chart['panchanga']['paksha']} {birth_chart['panchanga']['tithiName']} "
                  f"· {birth_chart['panchanga']['tithiPct']:.1f}%"),
        ("Nakṣatra", f"{NAKSHATRAS[birth_chart['panchanga']['nakIdx']]} · pada "
                      f"{birth_chart['panchanga']['nakPada']}"),
        ("Yoga", YOGAS[birth_chart["panchanga"]["yogaIdx"]]),
        ("Karaṇa", birth_chart["panchanga"]["karana"]),
        ("Ayanāṁśa", f"{fmt_deg(birth_chart['ayanDate'])} (Lahiri)"),
    ]
    rows_html = "".join(
        f'<div class="krow"><span class="kmuted">{k}</span><span>{v}</span></div>' for k, v in rows
    )
    st.markdown(
        f'<div class="kcard"><h4>Pañcāṅga · at birth</h4>{rows_html}'
        f'<p class="ksindoor" style="font-size:14px;margin-top:10px;">'
        f'Now: {tp["paksha"]} {tp["tithiName"]} · {NAKSHATRAS[tp["nakIdx"]]}</p></div>',
        unsafe_allow_html=True,
    )

# ---- Row 3: Graha Info table (full width, deva.guru style) ----------------
st.markdown('<div class="kcard"><h4>Graha Info</h4>', unsafe_allow_html=True)

header = (
    "<tr><th>Body</th><th>Kāraka</th><th>Long</th><th>Lat</th><th>Dec</th>"
    "<th>Nakṣatra</th><th>Pada</th><th>Transit now</th></tr>"
)
body_rows = []
for b in birth_chart["bodies"]:
    retro_mark = " ℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
    combust_mark = " 🔥" if b.get("combust") else ""
    long_str = f'{SIGN_ABBR[b["sign"]]} {fmt_dms(b["inSign"])}'
    nak_lord = DASHA_LORD_SHORT[b["nakIdx"] % 9]
    nak_str = f'{NAKSHATRAS[b["nakIdx"]]}<span class="kmuted">({b["nakIdx"]+1})</span> <span class="lord">{nak_lord}</span>'
    t = tdict[b["key"]]
    transit_str = (
        f'{SIGNS[t["sign"]]} {fmt_deg(t["inSign"])}'
        + (" ℞" if t["retro"] and b["key"] not in ("Ra", "Ke") else "")
    )
    body_rows.append(
        f'<tr><td class="body-key">{b["key"]}{retro_mark}{combust_mark}</td>'
        f'<td class="kmuted">{b["karaka"] or ""}</td>'
        f'<td style="font-family:monospace;">{long_str}</td>'
        f'<td class="kmuted" style="font-family:monospace;">{fmt_dms(b["lat"])}</td>'
        f'<td class="kmuted" style="font-family:monospace;">{fmt_dms(b["dec"])}</td>'
        f'<td>{nak_str}</td>'
        f'<td>{b["pada"]}</td>'
        f'<td class="ksindoor">{transit_str}</td></tr>'
    )

st.markdown(
    f'<div style="overflow-x:auto;"><table class="gtable">{header}{"".join(body_rows)}</table></div>'
    f'<p class="kmuted" style="font-size:13px;margin-top:10px;">'
    "Kāraka = classical 8-graha Chara Kāraka (AK=Ātmakāraka … DK=Dārakāraka). "
    "🔥 = combust (within classical orb of the Sun). ℞ = retrograde.</p></div>",
    unsafe_allow_html=True,
)

st.markdown(
    '<p class="kmuted" style="font-size:12px;">Engine accuracy: Sun/Moon a few arc-minutes, '
    "planets ~0.1–0.5°, mean Rāhu. For production, use Swiss Ephemeris + a geocoding API.</p>",
    unsafe_allow_html=True,
)

st.caption("Tip: click **🔄 Refresh transits** any time to update the red transit positions to right now.")
