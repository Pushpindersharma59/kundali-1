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

Worldwide birthplace search (recommended):
    pip install timezonefinder
    This enables offline, DST-and-history-aware timezone lookup for any
    latitude/longitude on Earth (via the IANA tz database), paired with
    live place search against OpenStreetMap Nominatim at runtime — together
    these cover essentially any city, town, or village worldwide, without
    needing a static database embedded in this file. If timezonefinder
    isn't installed, the app falls back to a cruder longitude/15 estimate.
"""

import math
import hashlib
import hmac
import os
import re
import secrets
import sqlite3
import time
import zoneinfo
from datetime import datetime, timedelta, date, time as dtime

import streamlit as st
import pandas as pd
import requests

try:
    from timezonefinder import TimezoneFinder
    _TZF = TimezoneFinder()
    HAS_TZFINDER = True
except ImportError:
    _TZF = None
    HAS_TZFINDER = False

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


_PLANET_NAME_MAP = {"Ma": "Mars", "Me": "Mercury", "Jp": "Jupiter", "Ve": "Venus", "Sa": "Saturn"}


def graha_sidereal_lon_at_jd(key: str, jd: float) -> float:
    """A single graha's sidereal longitude at a given Julian Day — mirrors
    compute_chart's exact per-key ayanamsa convention (Su/Mo/Ra/Ke use the
    date-varying ayanamsa(jd); the 5 classical planets use the fixed
    AYAN_J2000, matching how compute_chart already computes them, so this
    stays consistent with everything else the app displays)."""
    if key == "Su":
        return norm360(sun_longitude(jd) - ayanamsa(jd))
    if key == "Mo":
        return norm360(moon_longitude(jd) - ayanamsa(jd))
    if key == "Ra":
        return norm360(mean_node(jd) - ayanamsa(jd))
    if key == "Ke":
        return norm360(mean_node(jd) - ayanamsa(jd) + 180)
    return norm360(geo_longitude(_PLANET_NAME_MAP[key], jd) - AYAN_J2000)


NAK_SPAN = 360.0 / 27.0
# Coarse step size (days) and max search window (days) per graha, tuned to
# each one's typical speed through the zodiac — the Moon crosses a nakshatra
# in about a day, Saturn can take well over a year.
_NAK_SEARCH_STEP = {"Su": 0.5, "Mo": 0.05, "Ma": 1.0, "Me": 1.0, "Jp": 3.0, "Ve": 1.0, "Sa": 5.0, "Ra": 5.0, "Ke": 5.0}
_NAK_SEARCH_MAX_DAYS = {"Su": 25, "Mo": 3, "Ma": 400, "Me": 130, "Jp": 900, "Ve": 130, "Sa": 900, "Ra": 900, "Ke": 900}


def find_nakshatra_transition_jd(key: str, jd0: float, current_idx: int, search_forward: bool):
    """Steps through time from jd0 (forward or backward) until this graha's
    nakshatra index differs from current_idx, then bisects to pin down the
    transition moment precisely. Returns a Julian Day, or None if nothing
    was found within the search window (shouldn't normally happen given the
    per-graha window sizes above)."""
    step = _NAK_SEARCH_STEP[key] * (1 if search_forward else -1)
    n_steps = int(_NAK_SEARCH_MAX_DAYS[key] / _NAK_SEARCH_STEP[key])
    jd_same = jd0
    for i in range(1, n_steps + 1):
        jd_probe = jd0 + step * i
        idx_probe = int(graha_sidereal_lon_at_jd(key, jd_probe) // NAK_SPAN) % 27
        if idx_probe != current_idx:
            lo, hi = (jd_same, jd_probe) if search_forward else (jd_probe, jd_same)
            for _ in range(40):
                mid = (lo + hi) / 2
                mid_idx = int(graha_sidereal_lon_at_jd(key, mid) // NAK_SPAN) % 27
                if mid_idx == current_idx:
                    lo = mid
                else:
                    hi = mid
            return hi if search_forward else lo
        jd_same = jd_probe
    return None


def compute_nakshatra_transit_window(key: str, jd_now: float, nak_idx: int):
    """Returns (entry_jd_or_None, exit_jd_or_None) — when this graha entered
    its current nakshatra and when it will next leave it."""
    entry_jd = find_nakshatra_transition_jd(key, jd_now, nak_idx, search_forward=False)
    exit_jd = find_nakshatra_transition_jd(key, jd_now, nak_idx, search_forward=True)
    return entry_jd, exit_jd


def jd_to_local_date_str(jd: float, tz: float) -> str:
    """Julian Day (UT) -> a 'DD Mon YYYY' string in the given UTC offset."""
    local_dt = datetime(2000, 1, 1) + timedelta(days=(jd - julian_day(2000, 1, 1, 0.0))) + timedelta(hours=tz)
    return local_dt.strftime("%d %b %Y")


def jd_to_utc_datetime(jd: float) -> datetime:
    """Julian Day -> a plain (naive, UTC) Python datetime."""
    return datetime(2000, 1, 1) + timedelta(days=(jd - julian_day(2000, 1, 1, 0.0)))


def find_tithi_transition_jd(jd0: float, current_tithi_idx: int, search_forward: bool):
    """Same bisection idea as find_nakshatra_transition_jd, but tracking the
    tithi index (Sun-Moon elongation // 12°) instead of a graha's nakshatra —
    the tithi changes roughly once a day, so a small fixed step works fine."""
    step = 0.05 * (1 if search_forward else -1)  # ~72 minutes per coarse step
    n_steps = int(3 / 0.05)  # 3-day safety window either side
    jd_same = jd0

    def _tithi_idx(jd):
        elong = norm360(moon_longitude(jd) - sun_longitude(jd))
        return int(elong // 12) % 30

    for i in range(1, n_steps + 1):
        jd_probe = jd0 + step * i
        idx_probe = _tithi_idx(jd_probe)
        if idx_probe != current_tithi_idx:
            lo, hi = (jd_same, jd_probe) if search_forward else (jd_probe, jd_same)
            for _ in range(40):
                mid = (lo + hi) / 2
                if _tithi_idx(mid) == current_tithi_idx:
                    lo = mid
                else:
                    hi = mid
            return hi if search_forward else lo
        jd_same = jd_probe
    return None


NAKSHATRA_TRAITS_ASCII = [
    "swift, healing, pioneering", "restraining, transformative, intense",
    "sharp, purifying, determined", "growth-oriented, sensual, creative",
    "searching, gentle, curious", "stormy, transformative, emotional",
    "renewing, nurturing, optimistic", "nourishing, protective, disciplined",
    "intense, penetrating, secretive", "authoritative, traditional, ambitious",
    "pleasure-loving, creative, sociable", "generous, dependable, kind",
    "skillful, clever, resourceful", "brilliant, artistic, charismatic",
    "independent, flexible, diplomatic", "goal-driven, determined, competitive",
    "devoted, cooperative, balanced", "protective, responsible, courageous",
    "investigative, root-seeking, intense", "invincible, proud, persuasive",
    "enduring, principled, victorious", "attentive, learned, connective",
    "wealthy, rhythmic, ambitious", "healing, secretive, unconventional",
    "intense, transformative, passionate", "wise, deep, spiritually mature",
    "nurturing, compassionate, transitional",
]


def compute_nakshatra_live_data(lat: float, lon: float, tz: float) -> dict:
    """Everything the live nakshatra-clock widget needs, computed fresh from
    real ephemeris for right now — no hardcoded date window, works for any
    moment. Boundary timestamps are returned as ISO strings (in the given
    UTC offset) so client-side JS can interpolate a live-ticking display
    between them without any further server round-trips."""
    now_local = now_in_city(tz)
    jd_now = julian_day(now_local.year, now_local.month, now_local.day,
                         now_local.hour + now_local.minute / 60 + now_local.second / 3600 - tz)

    moon_lon_trop = moon_longitude(jd_now)
    sun_lon_trop = sun_longitude(jd_now)
    ayan = ayanamsa(jd_now)
    moon_sid = norm360(moon_lon_trop - ayan)
    nak_idx = int(moon_sid // NAK_SPAN) % 27
    nak_sign = int(moon_sid // 30)

    nak_entry_jd, nak_exit_jd = compute_nakshatra_transit_window("Mo", jd_now, nak_idx)
    if nak_entry_jd is None or nak_exit_jd is None:
        return {"ok": False}

    elong = norm360(moon_lon_trop - sun_lon_trop)
    tithi_idx = int(elong // 12) % 30
    tithi_entry_jd = find_tithi_transition_jd(jd_now, tithi_idx, search_forward=False)
    tithi_exit_jd = find_tithi_transition_jd(jd_now, tithi_idx, search_forward=True)
    paksha = "Krishna" if tithi_idx >= 15 else "Shukla"
    local_tithi_idx = tithi_idx if tithi_idx < 15 else tithi_idx - 15
    if local_tithi_idx == 14:
        tithi_name = "Purnima" if paksha == "Shukla" else "Amavasya"
    else:
        tithi_name = TITHIS_ASCII[local_tithi_idx]

    nak_start_lon = nak_idx * NAK_SPAN
    pada_span = NAK_SPAN / 4
    padas = []
    for i in range(4):
        p_start_jd = nak_entry_jd + i * (nak_exit_jd - nak_entry_jd) / 4
        p_end_jd = nak_entry_jd + (i + 1) * (nak_exit_jd - nak_entry_jd) / 4
        p_start_lon = norm360(nak_start_lon + i * pada_span)
        p_end_lon = norm360(nak_start_lon + (i + 1) * pada_span)
        p_mid_lon = norm360(nak_start_lon + (i + 0.5) * pada_span)
        p_sign = navamsa_sign(p_mid_lon)
        p_lord_key = RASHI_LORD.get(p_sign, "Su")
        padas.append({
            "sign": SIGNS_ASCII[p_sign], "lord": BODY_FULLNAME_ASCII.get(p_lord_key, p_lord_key),
            "lord_key": p_lord_key,
            "deg_start": round(p_start_lon % 30, 2), "deg_end": round(p_end_lon % 30 or 30, 2),
            "start_iso": (jd_to_utc_datetime(p_start_jd) + timedelta(hours=tz)).isoformat(),
            "end_iso": (jd_to_utc_datetime(p_end_jd) + timedelta(hours=tz)).isoformat(),
        })

    return {
        "ok": True,
        "nakshatra": NAKSHATRAS_ASCII[nak_idx], "nak_num": nak_idx + 1,
        "rashi": SIGNS_ASCII[nak_sign],
        "deg_start": round(nak_start_lon % 30, 2), "deg_end": round((nak_start_lon + NAK_SPAN) % 30 or 30, 2),
        "lord": BODY_FULLNAME_ASCII.get(DASHA_LORD_SHORT[nak_idx % 9], DASHA_LORD_SHORT[nak_idx % 9]),
        "lord_key": DASHA_LORD_SHORT[nak_idx % 9],
        "deity": NAKSHATRA_DEITY_ASCII[nak_idx], "traits": NAKSHATRA_TRAITS_ASCII[nak_idx],
        "nak_start_iso": (jd_to_utc_datetime(nak_entry_jd) + timedelta(hours=tz)).isoformat(),
        "nak_end_iso": (jd_to_utc_datetime(nak_exit_jd) + timedelta(hours=tz)).isoformat(),
        "tithi_name": tithi_name, "paksha": paksha,
        "tithi_start_iso": (jd_to_utc_datetime(tithi_entry_jd) + timedelta(hours=tz)).isoformat() if tithi_entry_jd else None,
        "tithi_end_iso": (jd_to_utc_datetime(tithi_exit_jd) + timedelta(hours=tz)).isoformat() if tithi_exit_jd else None,
        "elong": round(elong, 2),
        "padas": padas,
        "tz": tz,
    }


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


def get_historical_utc_offset(lat: float, lon: float, y: int, mo: int, dd: int,
                               hh: int, mm: int, ss: int = 0) -> float:
    """Real, DST-and-history-aware UTC offset for any lat/lon and any date, using
    timezonefinder (offline, ships its own worldwide timezone-boundary polygons)
    plus Python's built-in zoneinfo (the IANA tz database, which already encodes
    every historical DST rule change a place has ever had). This replaces a fixed
    per-city offset — which silently ignores daylight saving and any historical
    timezone-rule changes — with the offset that actually applied at that exact
    moment. Falls back to a crude longitude/15 estimate only if timezonefinder
    isn't installed or the lookup fails (e.g. open ocean coordinates)."""
    if HAS_TZFINDER and _TZF is not None:
        try:
            tzname = _TZF.timezone_at(lat=lat, lng=lon)
            if tzname:
                tz = zoneinfo.ZoneInfo(tzname)
                dt = datetime(y, mo, dd, hh, mm, ss, tzinfo=tz)
                offset = dt.utcoffset()
                if offset is not None:
                    return offset.total_seconds() / 3600
        except Exception:
            pass
    return round(lon / 15.0 * 4) / 4  # crude fallback, rounded to nearest 15 minutes


@st.cache_data(ttl=3600, show_spinner=False)
def geocode_place(query: str, limit: int = 8):
    """Live worldwide place search via OpenStreetMap Nominatim — covers
    essentially every city, town, and village on Earth (far beyond any static
    list this app could realistically embed), including alternate and local
    names. Cached per exact query string for an hour so repeated searches
    within a session don't re-hit the API. Requires the deployed app's own
    outbound internet access at runtime (works fine on Render; this call
    can't be exercised from a network-restricted dev/test sandbox)."""
    query = (query or "").strip()
    if len(query) < 2:
        return []
    try:
        resp = requests.get(
            "https://nominatim.openstreetmap.org/search",
            params={"q": query, "format": "jsonv2", "limit": limit, "addressdetails": 1},
            headers={"User-Agent": "KundaliApp/1.0 (Vedic astrology birth-chart tool)"},
            timeout=8,
        )
        resp.raise_for_status()
        out = []
        for item in resp.json():
            out.append({
                "display_name": item.get("display_name", ""),
                "lat": float(item["lat"]),
                "lon": float(item["lon"]),
            })
        return out
    except (requests.RequestException, ValueError, KeyError):
        return []


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

# ---- Chara Kāraka significations (what each of the 8 ranked positions means) ----
KARAKA_MEANINGS = {
    "AK": "Ātmakāraka — self, soul purpose",
    "AmK": "Amātyakāraka — career, counsel",
    "BK": "Bhrātṛkāraka — siblings, courage",
    "MK": "Mātṛkāraka — mother, home",
    "PiK": "Pitṛkāraka — father, ancestors",
    "PK": "Putrakāraka — children, intellect",
    "GK": "Jñātikāraka — relatives, obstacles",
    "DK": "Dārakāraka — spouse, partnerships",
}

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
        subs.append({"lord": DASHA_LORDS[lord_idx], "lordIdx": lord_idx, "from": cursor, "to": end, "yrs": yrs})
        cursor = end
    return subs


# ---- Śīrṣodaya / Pṛṣṭhodaya / Ubhayodaya — classical "rising type" of each
# rāśi, based on which part of the sign's figure crosses the horizon first.
# (Gemini, Leo, Virgo, Libra, Scorpio, Aquarius = head-rising; Aries, Taurus,
# Cancer, Sagittarius, Capricorn = back-rising; Pisces rises both ways.)
SIGN_RISING_TYPE = {
    2: "Śīrṣodaya", 4: "Śīrṣodaya", 5: "Śīrṣodaya", 6: "Śīrṣodaya", 7: "Śīrṣodaya", 10: "Śīrṣodaya",
    0: "Pṛṣṭhodaya", 1: "Pṛṣṭhodaya", 3: "Pṛṣṭhodaya", 8: "Pṛṣṭhodaya", 9: "Pṛṣṭhodaya",
    11: "Ubhayodaya",
}
SIGN_RISING_LABEL = {"Śīrṣodaya": "Head-Rising", "Pṛṣṭhodaya": "Tail/Back-Rising", "Ubhayodaya": "Both"}


def compute_running_dashas(birth_chart: dict, birth_bodies: list, at_dt: datetime = None):
    """Finds which Mahadasha, Antardasha, and Pratyantardasha are active
    right now (or at at_dt, if given), for the 'Running Now' display."""
    at_dt = at_dt or datetime.now()
    maha = next((d for d in birth_chart["dashas"] if d["from"] <= at_dt <= d["to"]), None)
    if maha is None:
        maha = birth_chart["dashas"][-1] if at_dt > birth_chart["dashas"][-1]["to"] else birth_chart["dashas"][0]

    antardashas = compute_antardashas(maha["lordIdx"], maha["from"], maha["yrs"])
    antar = next((a for a in antardashas if a["from"] <= at_dt <= a["to"]), antardashas[0])

    pratyantardashas = compute_pratyantardashas(antar["lordIdx"], antar["from"], antar["yrs"])
    pratyantar = next((p for p in pratyantardashas if p["from"] <= at_dt <= p["to"]), pratyantardashas[0])

    def _sign_for(lord_idx):
        key = DASHA_LORD_SHORT[lord_idx]
        body = next((b for b in birth_bodies if b["key"] == key), None)
        return body["sign"] if body else None

    return {
        "maha": maha, "antar": antar, "pratyantar": pratyantar,
        "maha_sign": _sign_for(maha["lordIdx"]), "antar_sign": _sign_for(antar["lordIdx"]),
        "pratyantar_sign": _sign_for(pratyantar["lordIdx"]),
    }


def _age_str(birth_dt: datetime, at_dt: datetime) -> str:
    days = (at_dt - birth_dt).days
    years = int(days / 365.25)
    months = int((days - years * 365.25) / 30.44)
    return f"{years}y {months}m"


def render_running_dashas(birth_chart: dict, birth_bodies: list, birth_dt: datetime):
    """The 'Running Now' card row: Mahadasha / Antardasha / Pratyantardasha
    currently active, each with its natal sign and classical rising-type."""
    now = datetime.now()
    rd = compute_running_dashas(birth_chart, birth_bodies, now)

    maha_name = DASHA_LORDS_ASCII[rd["maha"]["lordIdx"]]
    antar_name = DASHA_LORDS_ASCII[rd["antar"]["lordIdx"]]
    pratyantar_name = DASHA_LORDS_ASCII[rd["pratyantar"]["lordIdx"]]

    st.markdown(
        f'<p class="kmuted" style="font-weight:700;letter-spacing:0.05em;font-size:12px;margin-bottom:2px;">RUNNING NOW</p>'
        f'<p style="font-size:20px;margin:0 0 12px;">{maha_name} \u2192 {antar_name} \u2192 {pratyantar_name}</p>',
        unsafe_allow_html=True,
    )

    def _dasha_card(label, lord_name, sign_idx, entry, is_third_level=False):
        rising = SIGN_RISING_TYPE.get(sign_idx, "")
        rising_label = SIGN_RISING_LABEL.get(rising, "")
        pill_color = {"Śīrṣodaya": ("#DFF3E8", "#1E7B54"), "Pṛṣṭhodaya": ("#FBE6DE", "#B5502B"),
                      "Ubhayodaya": ("#E8E4F7", "#5B45A8")}.get(rising, ("#eee", "#555"))
        sign_html = ""
        if sign_idx is not None:
            sign_html = (
                f'<div style="display:inline-flex;align-items:center;gap:8px;background:{pill_color[0]};'
                f'color:{pill_color[1]};border-radius:10px;padding:6px 12px;margin:8px 0;">'
                f'<span style="width:9px;height:9px;border-radius:50%;background:{pill_color[1]};display:inline-block;"></span>'
                f'<span><b style="letter-spacing:0.03em;font-size:12px;">{SIGNS_ASCII[sign_idx].upper()} \u00b7 {rising.upper()}</b><br>'
                f'<span style="font-size:10.5px;opacity:0.85;">{rising_label.upper()}</span></span></div>'
            )
        if is_third_level:
            detail_html = '<p class="kmuted" style="font-size:13px;margin-top:6px;">third-level timing</p>'
        else:
            date_range = f'{entry["from"].strftime("%d %b %Y")} \u2014 {entry["to"].strftime("%d %b %Y")}'
            age_range = f'{_age_str(birth_dt, entry["from"])} \u2014 {_age_str(birth_dt, entry["to"])}' if label != "MAHADASHA NOW" else f'until Age {_age_str(birth_dt, entry["to"])}'
            detail_html = (
                f'<p class="kmuted" style="font-size:13px;margin-top:6px;">{date_range}</p>'
                f'<div style="display:inline-block;background:{C["panelSoft"]};border-radius:8px;padding:3px 10px;'
                f'font-size:12px;margin-top:4px;">Age {age_range}</div>'
            )
        return (
            f'<div style="flex:1;padding:16px 18px;{"border-left:1px solid " + C["line"] + ";" if label != "MAHADASHA NOW" else ""}">'
            f'<p class="kmuted" style="font-size:11px;font-weight:700;letter-spacing:0.05em;margin:0;">{label}</p>'
            f'<p style="font-size:26px;margin:6px 0 0;">{lord_name}</p>'
            f'{sign_html}{detail_html}</div>'
        )

    cards_html = (
        _dasha_card("MAHADASHA NOW", maha_name, rd["maha_sign"], rd["maha"])
        + _dasha_card("ANTARDASHA NOW", antar_name, rd["antar_sign"], rd["antar"])
        + _dasha_card("PRATYANTAR NOW", pratyantar_name, rd["pratyantar_sign"], rd["pratyantar"], is_third_level=True)
    )
    st.markdown(
        f'<div style="display:flex;background:{C["panel"]};border:1px solid {C["line"]};border-radius:14px;overflow:hidden;">'
        f'{cards_html}</div>',
        unsafe_allow_html=True,
    )
    st.caption(
        "\u26a0\ufe0f Vim\u015bottar\u012b Da\u015b\u0101 timing, computed from your birth chart. \u015a\u012br\u1e63odaya/"
        "P\u1e5b\u1e63\u1e6dhodaya is a classical sign-classification used in some interpretive traditions "
        "\u2014 shown here for the natal sign occupied by each running lord."
    )


SIGN_ABBR3 = ["Ari", "Tau", "Gem", "Can", "Leo", "Vir", "Lib", "Sco", "Sag", "Cap", "Aqu", "Pis"]
SIGN_RISING_SHORT = {"Śīrṣodaya": "Head", "Pṛṣṭhodaya": "Tail/Back", "Ubhayodaya": "Both"}


def _rising_pill(sign_idx, small=False):
    """A small colour-coded 'Sign · Rising-type' pill, reused across the
    Dasha Explorer's Level 1/2/3 rows."""
    if sign_idx is None:
        return ""
    rising = SIGN_RISING_TYPE.get(sign_idx, "")
    bg, fg = {"Śīrṣodaya": ("#DFF3E8", "#1E7B54"), "Pṛṣṭhodaya": ("#FBE6DE", "#B5502B"),
              "Ubhayodaya": ("#E8E4F7", "#5B45A8")}.get(rising, ("#eee", "#555"))
    label = SIGN_ABBR3[sign_idx] + " \u00b7 " + SIGN_RISING_SHORT.get(rising, "")
    pad = "4.5px 13px" if small else "6px 16px"
    fs = "17px" if small else "19px"
    return (
        f'<span style="display:inline-flex;align-items:center;gap:5px;background:{bg};color:{fg};'
        f'border-radius:8px;padding:{pad};font-weight:700;font-size:{fs};white-space:nowrap;">'
        f'<span style="width:7px;height:7px;border-radius:50%;background:#fff;border:1.5px solid {fg};display:inline-block;"></span>'
        f'{label}</span>'
    )


PLANET_LIGHT_BG = {
    "Su": "#FDEBD0", "Mo": "#D6EAF8", "Ma": "#FADBD8", "Me": "#D5F5E3",
    "Jp": "#FCF3CF", "Ve": "#FDEDEC", "Sa": "#EFE3D3", "Ra": "#EBDCF3", "Ke": "#EBDCF3",
}
PLANET_LIGHT_BORDER = {
    "Su": "#E67E22", "Mo": "#5DADE2", "Ma": "#E74C3C", "Me": "#2ECC71",
    "Jp": "#F1C40F", "Ve": "#F1948A", "Sa": "#8B5E3C", "Ra": "#8E44AD", "Ke": "#8E44AD",
}


def render_dasha_explorer(birth_chart: dict, birth_bodies: list, birth_dt: datetime):
    """A fuller drill-down beneath the compact 'Running Now' row: the active
    Mahadasha as a header bar, every Antardasha within it (Level 2, with the
    currently-active one highlighted), and every Pratyantardasha within the
    currently-active Antardasha (Level 3, as a highlighted grid) — all
    reusing the same Vimśottarī Daśā engine and rising-type classification
    as 'Running Now' above, just showing the full sibling list at each level
    instead of only the single active period."""
    now = datetime.now()
    rd = compute_running_dashas(birth_chart, birth_bodies, now)
    maha, antar = rd["maha"], rd["antar"]
    maha_name = DASHA_LORDS_ASCII[maha["lordIdx"]]

    def _sign_for(lord_idx):
        key = DASHA_LORD_SHORT[lord_idx]
        body = next((b for b in birth_bodies if b["key"] == key), None)
        return body["sign"] if body else None

    maha_sign = _sign_for(maha["lordIdx"])
    maha_dur_yrs = round(maha["yrs"], 1)

    # ---- Level 1: current Mahadasha header bar ----
    st.markdown(
        f'<div style="background:{C["panelSoft"]};border:1px solid {C["line"]};border-radius:14px 14px 0 0;'
        f'padding:20px 22px;display:flex;justify-content:space-between;align-items:flex-start;">'
        f'<div>'
        f'<div style="display:flex;align-items:center;gap:14px;">'
        f'<div style="width:53px;height:53px;border-radius:50%;background:#fff;border:2px solid {C["gold"]};'
        f'display:flex;align-items:center;justify-content:center;font-weight:700;font-size:15px;color:{C["gold"]};">'
        f'{DASHA_LORD_SHORT[maha["lordIdx"]]}</div>'
        f'<span style="font-size:42px;font-weight:700;">{maha_name}</span></div>'
        f'<div style="margin-top:10px;">{_rising_pill(maha_sign)}</div>'
        f'<p class="kmuted" style="margin:10px 0 4px;font-size:18px;">{maha["from"].strftime("%d %b %Y")} \u2014 {maha["to"].strftime("%d %b %Y")}</p>'
        f'<div style="display:inline-block;background:{C["panel"]};border-radius:8px;padding:5px 12px;font-size:16.5px;">'
        f'Age {_age_str(birth_dt, maha["from"])} \u2014 Age {_age_str(birth_dt, maha["to"])}</div>'
        f'</div>'
        f'<div style="text-align:right;">'
        f'<p class="kmuted" style="font-size:15px;font-weight:700;letter-spacing:0.05em;margin:0;">DURATION</p>'
        f'<p style="font-size:30px;font-weight:700;margin:4px 0;">{maha_dur_yrs} years</p>'
        f'<p style="color:{C["sindoor"]};font-weight:700;font-size:16.5px;margin:0;">Active now</p>'
        f'</div></div>',
        unsafe_allow_html=True,
    )

    # ---- Level 2: all 9 Antardashas within the active Mahadasha ----
    antardashas = compute_antardashas(maha["lordIdx"], maha["from"], maha["yrs"])
    lcol, rcol = st.columns([1, 1.35])
    with lcol:
        st.markdown(
            f'<div style="background:{C["panel"]};border:1px solid {C["line"]};border-top:none;padding:16px 18px;height:100%;">'
            f'<div style="display:flex;justify-content:space-between;">'
            f'<p class="kmuted" style="font-size:16.5px;font-weight:700;letter-spacing:0.05em;margin:0;">LEVEL 2</p>'
            f'<p class="kmuted" style="font-size:18px;margin:0;">9 periods</p></div>'
            f'<p style="font-size:28.5px;font-weight:700;margin:4px 0 12px;">Antardashas</p>',
            unsafe_allow_html=True,
        )
        rows = []
        for a in antardashas:
            is_now = a["from"] <= now <= a["to"]
            lord_key = DASHA_LORD_SHORT[a["lordIdx"]]
            bg = PLANET_LIGHT_BG.get(lord_key, C["panelSoft"])
            border = f'2px solid {PLANET_LIGHT_BORDER.get(lord_key, C["gold"])}' if is_now else "2px solid transparent"
            now_badge = (f'<span style="background:{C["gold"]};color:#fff;font-size:15px;font-weight:700;'
                         f'border-radius:6px;padding:3px 12px;float:right;">NOW</span>') if is_now else ""
            a_sign = _sign_for(a["lordIdx"])
            rows.append(
                f'<div style="background:{bg};border:{border};border-radius:10px;padding:16px 14px;margin-bottom:8px;">'
                f'<div style="display:flex;align-items:center;gap:14px;">'
                f'<div style="width:33px;height:33px;border-radius:50%;background:#fff;border:1px solid {C["line"]};'
                f'display:flex;align-items:center;justify-content:center;font-size:13px;font-weight:700;">'
                f'{lord_key}</div>'
                f'<span style="font-weight:700;flex-shrink:0;font-size:21px;">{DASHA_LORDS_ASCII[a["lordIdx"]]}</span>'
                f'{_rising_pill(a_sign, small=True)}{now_badge}</div>'
                f'<div style="display:flex;justify-content:space-between;margin-top:10px;padding-left:47px;">'
                f'<span class="kmuted" style="font-size:18px;">{a["from"].strftime("%d %b %Y")} \u2014 {a["to"].strftime("%d %b %Y")}</span>'
                f'<span style="text-align:right;font-size:18px;">'
                f'<span class="kmuted">Age {_age_str(birth_dt, a["from"])}</span><br>'
                f'<b>{round(a["yrs"], 2)} years</b></span></div></div>'
            )
        st.markdown("".join(rows) + "</div>", unsafe_allow_html=True)

    # ---- Level 3: all 9 Pratyantardashas within the active Antardasha ----
    pratyantardashas = compute_pratyantardashas(antar["lordIdx"], antar["from"], antar["yrs"])
    antar_sign = _sign_for(antar["lordIdx"])
    with rcol:
        st.markdown(
            f'<div style="background:{C["panel"]};border:1px solid {C["line"]};border-top:none;border-left:none;'
            f'padding:16px 18px;height:100%;">'
            f'<div style="display:flex;justify-content:space-between;">'
            f'<p class="kmuted" style="font-size:16.5px;font-weight:700;letter-spacing:0.05em;margin:0;">LEVEL 3</p>'
            f'<p class="kmuted" style="font-size:18px;margin:0;">{antar["from"].strftime("%d %b %Y")} \u2014 {antar["to"].strftime("%d %b %Y")}</p></div>'
            f'<p style="font-size:28.5px;font-weight:700;margin:4px 0 8px;">{DASHA_LORDS_ASCII[antar["lordIdx"]]} Pratyantardashas</p>'
            f'<div style="display:flex;align-items:center;gap:8px;margin-bottom:14px;">'
            f'{_rising_pill(maha_sign, small=True)}<span class="kmuted" style="font-size:18px;">\u203a</span>{_rising_pill(antar_sign, small=True)}</div>',
            unsafe_allow_html=True,
        )
        p_cards = []
        for p in pratyantardashas:
            is_now = p["from"] <= now <= p["to"]
            p_lord_key = DASHA_LORD_SHORT[p["lordIdx"]]
            bg = PLANET_LIGHT_BG.get(p_lord_key, C["panelSoft"])
            border = f'3px solid {PLANET_LIGHT_BORDER.get(p_lord_key, C["gold"])}' if is_now else "1px solid " + C["line"]
            now_badge = (f'<span style="position:absolute;top:8px;right:8px;background:{C["gold"]};color:#fff;'
                         f'font-size:13.5px;font-weight:700;border-radius:6px;padding:2px 9px;">NOW</span>') if is_now else ""
            p_sign = _sign_for(p["lordIdx"])
            p_cards.append(
                f'<div style="position:relative;background:{bg};border:{border};border-radius:10px;'
                f'padding:18px;min-width:0;">'
                f'{now_badge}'
                f'<div style="width:30px;height:30px;border-radius:50%;background:#fff;border:1px solid {C["line"]};'
                f'display:flex;align-items:center;justify-content:center;font-size:11px;font-weight:700;margin-bottom:10px;">'
                f'{p_lord_key}</div>'
                f'<div style="font-weight:700;font-size:21px;margin-bottom:10px;">{DASHA_LORDS_ASCII[p["lordIdx"]]}</div>'
                f'{_rising_pill(p_sign, small=True)}'
                f'<p class="kmuted" style="font-size:15px;margin:12px 0 6px;">{p["from"].strftime("%d %b %Y")} \u2014 {p["to"].strftime("%d %b %Y")}</p>'
                f'<p class="kmuted" style="font-size:15px;margin:0;">Age {_age_str(birth_dt, p["from"])}</p>'
                f'</div>'
            )
        grid_rows = []
        for i in range(0, 9, 3):
            row_cells = "".join(f'<td style="width:33.33%;padding:5px;vertical-align:top;">{c}</td>' for c in p_cards[i:i + 3])
            grid_rows.append(f'<tr>{row_cells}</tr>')
        st.markdown(
            f'<table style="width:100%;border-collapse:separate;border-spacing:0;table-layout:fixed;">'
            f'{"".join(grid_rows)}</table></div>',
            unsafe_allow_html=True,
        )

    st.caption(
        "\u26a0\ufe0f Full Vim\u015bottar\u012b Da\u015b\u0101 breakdown \u2014 Level 2 shows every Antardash\u0101 within "
        "the currently active Mah\u0101da\u015b\u0101, Level 3 shows every Pratyantardash\u0101 within the currently "
        "active Antardash\u0101. The highlighted period in each level is the one running right now."
    )


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


HINDI_BODY_ABBR = {
    "As": "\u0932", "Su": "\u0938\u0942", "Mo": "\u091a\u0902", "Ma": "\u092e\u0902",
    "Me": "\u092c\u0941", "Jp": "\u0917\u0941", "Ve": "\u0936\u0941", "Sa": "\u0936",
    "Ra": "\u0930\u093e", "Ke": "\u0915\u0947",
}


def build_svg_chart(birth_bodies, transit_bodies, asc_sign: int, show_nakshatra: bool = False,
                     language: str = "English", show_transits: bool = True) -> str:
    """North Indian diamond chart. Each house lays its planets out in an
    adaptive grid (columns chosen from how many entries share that house)
    instead of a single vertical stack, with font size shrinking as the
    count grows — a crowded house (e.g. several birth + transit grahas all
    sharing one sign) previously overflowed the diamond's boundary; this
    keeps everything inside it. language="Hindi" swaps planet labels to
    Devanagari abbreviations; show_transits=False omits transit bodies."""
    by_house = [{"b": [], "t": []} for _ in range(12)]
    for x in birth_bodies:
        by_house[(x["sign"] - asc_sign + 12) % 12]["b"].append(x)
    if show_transits:
        for x in transit_bodies:
            if x["key"] == "As":
                continue
            by_house[(x["sign"] - asc_sign + 12) % 12]["t"].append(x)

    def label(x, kind, cx, y, font_size, sub_size):
        fill = C["sindoor"] if kind == "t" else (C["moon"] if x["key"] == "As" else C["ivory"])
        sub_fill = C["sindoor"] if kind == "t" else C["muted"]
        retro_mark = "\u211e" if (x["retro"] and x["key"] not in ("Ra", "Ke")) else ""
        deg = math.floor(x["inSign"])
        key_label = HINDI_BODY_ABBR.get(x["key"], x["key"]) if language == "Hindi" else x["key"]
        nak_line = ""
        if show_nakshatra and x["key"] != "As":
            nak_abbr = NAK_ABBR[x["nakIdx"]]
            nak_size = max(sub_size - 1.5, 6)
            nak_line = (
                f'<tspan x="{cx}" dy="{sub_size + 2}" font-size="{nak_size}" fill="{sub_fill}" '
                f'font-family="Georgia, serif">{nak_abbr}</tspan>'
            )
        return (
            f'<text x="{cx}" y="{y}" text-anchor="middle" font-size="{font_size}" font-weight="700" '
            f'fill="{fill}" font-family="Georgia, serif">{key_label}'
            f'<tspan font-size="{sub_size}" fill="{sub_fill}" font-family="monospace">'
            f' {deg}\u00b0{retro_mark}</tspan>{nak_line}</text>'
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

    # (max_n, columns, font_size, sub_size, row_height, col_width) — tuned so
    # even a heavily-crowded house (birth + transit grahas sharing one sign)
    # stays compact and visually separated from its neighbours, rather than
    # spreading into the next house's triangular space.
    LAYOUT_TIERS = [
        (2, 1, 15.5, 11, 25 if show_nakshatra else 15, 0),
        (3, 1, 14, 10, 21 if show_nakshatra else 14, 0),
        (4, 2, 12, 8.5, 19 if show_nakshatra else 12.5, 56),
        (6, 2, 10.5, 7.5, 16.5 if show_nakshatra else 11, 50),
        (9, 3, 9, 7, 14.5 if show_nakshatra else 9.5, 42),
        (99, 3, 8, 6, 13 if show_nakshatra else 8.5, 38),
    ]

    chart_center = (200, 200)
    for h, (cx0, cy0) in enumerate(HOUSE_CENTERS):
        sign_num = ((asc_sign + h) % 12) + 1
        b, t = by_house[h]["b"], by_house[h]["t"]
        entries = [(x, "b") for x in b] + [(x, "t") for x in t]
        n = len(entries)
        if n == 0:
            parts.append(f'<text x="{cx0}" y="{cy0 - 8}" text-anchor="middle" font-size="10" '
                          f'fill="{C["muted"]}" font-family="monospace">{sign_num}</text>')
            continue

        cols, font_size, sub_size, row_h, col_w = next(
            (c, fs, ss, rh, cw) for max_n, c, fs, ss, rh, cw in LAYOUT_TIERS if n <= max_n
        )

        # Push crowded houses outward from the chart's centre (away from
        # whichever neighbour sits toward the middle), so two crowded houses
        # near each other gain separation instead of their boxes touching.
        if n >= 4:
            dx, dy = cx0 - chart_center[0], cy0 - chart_center[1]
            dist = math.hypot(dx, dy) or 1
            push = min(6 + (n - 4) * 2, 22)
            cx, cy = cx0 + (dx / dist) * push, cy0 + (dy / dist) * push
        else:
            cx, cy = cx0, cy0

        rows = math.ceil(n / cols)
        total_h = rows * row_h
        total_w = cols * col_w if cols > 1 else font_size * 3.4
        start_y = cy - total_h / 2 + row_h * 0.7

        # Subtle background box behind this house's whole cluster — makes it
        # visually unambiguous which entries belong together even when two
        # crowded houses sit close to each other near the diamond's center.
        if n >= 4:
            box_pad_x, box_pad_y = 6, 5
            parts.append(
                f'<rect x="{cx - total_w/2 - box_pad_x:.1f}" y="{start_y - row_h*0.75 - box_pad_y:.1f}" '
                f'width="{total_w + box_pad_x*2:.1f}" height="{total_h + box_pad_y*2:.1f}" '
                f'rx="6" fill="#FFFFFF" fill-opacity="0.55" stroke="{C["gold"]}" stroke-width="0.6" stroke-opacity="0.35"/>'
            )

        parts.append(
            f'<text x="{cx}" y="{start_y - row_h - 2}" text-anchor="middle" font-size="10" '
            f'fill="{C["muted"]}" font-family="monospace">{sign_num}</text>'
        )
        for i, (x, kind) in enumerate(entries):
            row = i // cols
            col = i % cols
            n_in_row = min(cols, n - row * cols)
            row_x = cx + (col - (n_in_row - 1) / 2) * col_w
            row_y = start_y + row * row_h
            parts.append(label(x, kind, row_x, row_y, font_size, sub_size))

    parts.append("</svg>")
    return "".join(parts)


# ---- Per-graha transit colors (birth positions always stay black/ivory) ----
PLANET_TRANSIT_COLORS = {
    "Su": "#E67E22",  # orange
    "Mo": "#7EC8E3",  # light blue
    "Ma": "#E74C3C",  # red
    "Me": "#2ECC71",  # green
    "Jp": "#F1C40F",  # yellow
    "Ve": "#F1948A",  # light red
    "Sa": "#8B5E3C",  # brown
    "Ra": "#8E44AD",  # purple
    "Ke": "#8E44AD",  # purple (paired with Rahu — not individually specified)
}


def build_combined_diamond_svg(birth_bodies, transit_bodies, asc_sign: int) -> str:
    """A single diamond chart with birth AND transit grahas merged into one
    ascending-by-degree list per house. Birth stays black/ivory; each transit
    graha gets its own fixed colour (PLANET_TRANSIT_COLORS) instead of one
    uniform transit colour."""
    by_house = [[] for _ in range(12)]
    for x in birth_bodies:
        by_house[(x["sign"] - asc_sign + 12) % 12].append(dict(x, _is_transit=False))
    for x in transit_bodies:
        if x["key"] == "As":
            continue
        by_house[(x["sign"] - asc_sign + 12) % 12].append(dict(x, _is_transit=True))
    for entries in by_house:
        entries.sort(key=lambda b: b["inSign"])

    def label(x, cx, y):
        is_t = x["_is_transit"]
        fill = PLANET_TRANSIT_COLORS.get(x["key"], C["sindoor"]) if is_t else (
            C["moon"] if x["key"] == "As" else C["ivory"]
        )
        sub_fill = fill if is_t else C["muted"]
        retro_mark = "℞" if (x["retro"] and x["key"] not in ("Ra", "Ke")) else ""
        deg = math.floor(x["inSign"])
        return (
            f'<text x="{cx}" y="{y}" text-anchor="middle" font-size="13" font-weight="700" '
            f'fill="{fill}" font-family="Georgia, serif">{x["key"]}'
            f'<tspan font-size="9.5" fill="{sub_fill}" font-family="monospace">'
            f' {deg}°{retro_mark}</tspan></text>'
        )

    parts = [
        '<svg viewBox="0 0 400 400" width="720" height="720" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="cbg2" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDE7" /><stop offset="100%" stop-color="#FFF3B0" />'
        '</radialGradient></defs>',
        f'<rect x="2" y="2" width="396" height="396" fill="url(#cbg2)" stroke="{C["gold"]}" stroke-width="2" />',
        f'<line x1="2" y1="2" x2="398" y2="398" stroke="{C["gold"]}" stroke-width="1" opacity="0.85" />',
        f'<line x1="398" y1="2" x2="2" y2="398" stroke="{C["gold"]}" stroke-width="1" opacity="0.85" />',
        f'<polygon points="200,2 398,200 200,398 2,200" fill="none" stroke="{C["gold"]}" '
        f'stroke-width="1" opacity="0.85" />',
    ]

    step = 15
    for h, (cx, cy) in enumerate(HOUSE_CENTERS):
        sign_num = ((asc_sign + h) % 12) + 1
        entries = by_house[h]
        n = len(entries)
        start_y = cy - ((n - 1) * step) / 2 + 4
        parts.append(
            f'<text x="{cx}" y="{start_y - step - 2}" text-anchor="middle" font-size="10" '
            f'fill="{C["muted"]}" font-family="monospace">{sign_num}</text>'
        )
        for i, x in enumerate(entries):
            parts.append(label(x, cx, start_y + i * step))

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
os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)

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
            email TEXT,
            email_lower TEXT,
            phone TEXT,
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
            gender TEXT,
            updated_at REAL,
            FOREIGN KEY(user_id) REFERENCES users(id)
        )
    """)

    # ---- Migration: add gender to profiles if this DB predates the field.
    profile_cols = {row["name"] for row in conn.execute("PRAGMA table_info(profiles)").fetchall()}
    if "gender" not in profile_cols:
        conn.execute("ALTER TABLE profiles ADD COLUMN gender TEXT")

    # ---- Migration: bring an existing "users" table up to the current schema
    # (username_lower for case-insensitive login, email/email_lower for
    # account recovery). Nullable columns only — SQLite can't add a NOT NULL
    # column with no default to a table that already has rows.
    cols_info = conn.execute("PRAGMA table_info(users)").fetchall()
    existing_cols = {row["name"] for row in cols_info}

    if "username_lower" not in existing_cols:
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

    if "email" not in existing_cols:
        conn.execute("ALTER TABLE users ADD COLUMN email TEXT")
    if "email_lower" not in existing_cols:
        conn.execute("ALTER TABLE users ADD COLUMN email_lower TEXT")
        conn.execute("UPDATE users SET email_lower = lower(email) WHERE email IS NOT NULL AND email_lower IS NULL")
    # De-dupe any pre-existing collisions before adding the unique index, else the
    # CREATE UNIQUE INDEX call itself would fail.
    email_dupes = conn.execute("""
        SELECT email_lower FROM users
        WHERE email_lower IS NOT NULL AND email_lower != ''
        GROUP BY email_lower HAVING COUNT(*) > 1
    """).fetchall()
    for row in email_dupes:
        ids = [r["id"] for r in conn.execute(
            "SELECT id FROM users WHERE email_lower=? ORDER BY id", (row["email_lower"],)
        ).fetchall()]
        for extra_id in ids[1:]:
            conn.execute("UPDATE users SET email=NULL, email_lower=NULL WHERE id=?", (extra_id,))
    conn.execute(
        "CREATE UNIQUE INDEX IF NOT EXISTS idx_users_email_lower ON users(email_lower) "
        "WHERE email_lower IS NOT NULL AND email_lower != ''"
    )

    if "phone" not in existing_cols:
        conn.execute("ALTER TABLE users ADD COLUMN phone TEXT")
    phone_dupes = conn.execute("""
        SELECT phone FROM users WHERE phone IS NOT NULL AND phone != ''
        GROUP BY phone HAVING COUNT(*) > 1
    """).fetchall()
    for row in phone_dupes:
        ids = [r["id"] for r in conn.execute(
            "SELECT id FROM users WHERE phone=? ORDER BY id", (row["phone"],)
        ).fetchall()]
        for extra_id in ids[1:]:
            conn.execute("UPDATE users SET phone=NULL WHERE id=?", (extra_id,))
    conn.execute(
        "CREATE UNIQUE INDEX IF NOT EXISTS idx_users_phone ON users(phone) "
        "WHERE phone IS NOT NULL AND phone != ''"
    )

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

    # ---- Daily free-tier usage counter: one row per (user, calendar date).
    # Non-premium accounts are capped at FREE_DAILY_LIMIT chart generations
    # per day; premium accounts are never checked against this table.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS chart_usage (
            user_id INTEGER NOT NULL,
            usage_date TEXT NOT NULL,
            count INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY (user_id, usage_date),
            FOREIGN KEY(user_id) REFERENCES users(id)
        )
    """)

    # ---- Saved chart library: unlike "profiles" (one saved birth-detail set
    # per account, used to prefill the form), this holds any number of named
    # charts per user — e.g. family members or repeat clients — that can be
    # reloaded into the form at any time.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS saved_charts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            label TEXT NOT NULL,
            name TEXT, dob TEXT NOT NULL, tob TEXT NOT NULL,
            city_name TEXT, city_region TEXT, lat REAL, lon REAL, tz REAL,
            created_at REAL NOT NULL,
            FOREIGN KEY(user_id) REFERENCES users(id)
        )
    """)

    # ---- "Remember Me" tokens: only the SHA-256 hash is stored, never the raw
    # token (same principle as password storage) — the raw token only ever
    # lives in the user's browser URL, generated fresh on each sign-in.
    conn.execute("""
        CREATE TABLE IF NOT EXISTS remember_tokens (
            token_hash TEXT PRIMARY KEY,
            user_id INTEGER NOT NULL,
            expires_at REAL NOT NULL,
            created_at REAL NOT NULL,
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


EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")
PHONE_RE = re.compile(r"^\+?[0-9]{7,15}$")


def username_taken(username: str) -> bool:
    conn = get_conn()
    row = conn.execute(
        "SELECT 1 FROM users WHERE username_lower=?", (username.lower(),)
    ).fetchone()
    conn.close()
    return row is not None


def email_taken(email: str) -> bool:
    conn = get_conn()
    row = conn.execute(
        "SELECT 1 FROM users WHERE email_lower=?", (email.lower(),)
    ).fetchone()
    conn.close()
    return row is not None


def phone_taken(phone: str) -> bool:
    conn = get_conn()
    row = conn.execute("SELECT 1 FROM users WHERE phone=?", (phone,)).fetchone()
    conn.close()
    return row is not None


def create_user(username: str, password: str, email: str = "", phone: str = ""):
    """Returns (ok, message). Email and phone are both optional but, if
    given, must be validly formatted and unique."""
    conn = get_conn()
    pw_hash, pw_salt = hash_password(password)
    email_clean = email.strip() or None
    email_lower = email_clean.lower() if email_clean else None
    phone_clean = phone.strip() or None
    try:
        conn.execute(
            "INSERT INTO users (username, username_lower, email, email_lower, phone, pw_hash, pw_salt, created_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (username, username.lower(), email_clean, email_lower, phone_clean, pw_hash, pw_salt, time.time()),
        )
        conn.commit()
        return True, ""
    except sqlite3.IntegrityError:
        if email_lower and email_taken(email):
            return False, "That email is already registered — try logging in instead."
        if phone_clean and phone_taken(phone_clean):
            return False, "That phone number is already registered — try logging in instead."
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


# ---- Free-tier daily chart-generation limit ---------------------------------
FREE_DAILY_LIMIT = 3


def get_today_usage_count(user_id: int) -> int:
    conn = get_conn()
    today = date.today().isoformat()
    row = conn.execute(
        "SELECT count FROM chart_usage WHERE user_id=? AND usage_date=?", (user_id, today)
    ).fetchone()
    conn.close()
    return row["count"] if row else 0


def increment_usage(user_id: int) -> int:
    """Increments today's counter for this user and returns the new count."""
    conn = get_conn()
    today = date.today().isoformat()
    conn.execute(
        """
        INSERT INTO chart_usage (user_id, usage_date, count) VALUES (?, ?, 1)
        ON CONFLICT(user_id, usage_date) DO UPDATE SET count = count + 1
        """,
        (user_id, today),
    )
    row = conn.execute(
        "SELECT count FROM chart_usage WHERE user_id=? AND usage_date=?", (user_id, today)
    ).fetchone()
    conn.commit()
    conn.close()
    return row["count"] if row else 1


def load_profile(user_id: int):
    conn = get_conn()
    row = conn.execute("SELECT * FROM profiles WHERE user_id=?", (user_id,)).fetchone()
    conn.close()
    return dict(row) if row else None


def save_profile(user_id: int, name, dob_iso, tob_iso, city_name, city_region, lat, lon, tz, gender=""):
    conn = get_conn()
    conn.execute(
        """
        INSERT INTO profiles (user_id, name, dob, tob, city_name, city_region, lat, lon, tz, gender, updated_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            name=excluded.name, dob=excluded.dob, tob=excluded.tob,
            city_name=excluded.city_name, city_region=excluded.city_region,
            lat=excluded.lat, lon=excluded.lon, tz=excluded.tz, gender=excluded.gender,
            updated_at=excluded.updated_at
        """,
        (user_id, name, dob_iso, tob_iso, city_name, city_region, lat, lon, tz, gender, time.time()),
    )
    conn.commit()
    conn.close()


def save_chart_to_library(user_id: int, label: str, name: str, dob_iso: str, tob_iso: str,
                           city_name: str, city_region: str, lat: float, lon: float, tz: float) -> int:
    """Adds a new entry to the user's chart library (unlike save_profile, this
    never overwrites — every save creates a new row, so multiple charts can
    be kept side by side). Returns the new row's id."""
    conn = get_conn()
    cur = conn.execute(
        """
        INSERT INTO saved_charts (user_id, label, name, dob, tob, city_name, city_region, lat, lon, tz, created_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (user_id, label, name, dob_iso, tob_iso, city_name, city_region, lat, lon, tz, time.time()),
    )
    conn.commit()
    new_id = cur.lastrowid
    conn.close()
    return new_id


def list_saved_charts(user_id: int):
    conn = get_conn()
    rows = conn.execute(
        "SELECT * FROM saved_charts WHERE user_id=? ORDER BY created_at DESC", (user_id,)
    ).fetchall()
    conn.close()
    return [dict(r) for r in rows]


def get_saved_chart(chart_id: int, user_id: int):
    conn = get_conn()
    row = conn.execute(
        "SELECT * FROM saved_charts WHERE id=? AND user_id=?", (chart_id, user_id)
    ).fetchone()
    conn.close()
    return dict(row) if row else None


def delete_saved_chart(chart_id: int, user_id: int):
    conn = get_conn()
    conn.execute("DELETE FROM saved_charts WHERE id=? AND user_id=?", (chart_id, user_id))
    conn.commit()
    conn.close()


REMEMBER_ME_DAYS = 30


def _hash_token(raw_token: str) -> str:
    return hashlib.sha256(raw_token.encode("utf-8")).hexdigest()


def create_remember_token(user_id: int) -> str:
    """Generates a fresh high-entropy token, stores only its hash (with a 30-day
    expiry), and returns the raw token — the raw value is meant to go straight
    into the browser's URL via st.query_params and never be stored server-side."""
    raw_token = secrets.token_urlsafe(32)
    conn = get_conn()
    conn.execute(
        "INSERT INTO remember_tokens (token_hash, user_id, expires_at, created_at) VALUES (?, ?, ?, ?)",
        (_hash_token(raw_token), user_id, time.time() + REMEMBER_ME_DAYS * 86400, time.time()),
    )
    conn.commit()
    conn.close()
    return raw_token


def validate_remember_token(raw_token: str):
    """Returns the user dict if the token is valid and unexpired, else None.
    Expired tokens are opportunistically cleaned up here too."""
    if not raw_token:
        return None
    conn = get_conn()
    token_hash = _hash_token(raw_token)
    row = conn.execute(
        "SELECT user_id, expires_at FROM remember_tokens WHERE token_hash=?", (token_hash,)
    ).fetchone()
    if row is None:
        conn.close()
        return None
    if row["expires_at"] < time.time():
        conn.execute("DELETE FROM remember_tokens WHERE token_hash=?", (token_hash,))
        conn.commit()
        conn.close()
        return None
    user_row = conn.execute("SELECT * FROM users WHERE id=?", (row["user_id"],)).fetchone()
    conn.close()
    return dict(user_row) if user_row else None


def revoke_remember_token(raw_token: str):
    if not raw_token:
        return
    conn = get_conn()
    conn.execute("DELETE FROM remember_tokens WHERE token_hash=?", (_hash_token(raw_token),))
    conn.commit()
    conn.close()


init_db()

# ---- Demo/reviewer account -------------------------------------------------
# Payment gateways (Razorpay, etc.) often need to log in and click through the
# live site during account activation review. Rather than share a real user's
# password, seed one fixed, low-privilege account they can use. It behaves
# exactly like any other account (own password hash, no special powers) —
# nothing else in the app treats it differently.
DEMO_USERNAME = "razorpay_demo"
DEMO_PASSWORD = "Demo@12345"


def seed_demo_account():
    if not username_taken(DEMO_USERNAME):
        create_user(DEMO_USERNAME, DEMO_PASSWORD)


seed_demo_account()

# ---- Ready-made premium account, for your own testing ----------------------
# Logs straight in with premium already unlocked — no payment flow needed to
# see the Nakṣatra-on-chart, divisional charts (D2–D60), or PDF/HTML report.
PREMIUM_DEMO_USERNAME = "premium_demo"
PREMIUM_DEMO_PASSWORD = "Demo@12345"


def seed_premium_demo_account():
    if not username_taken(PREMIUM_DEMO_USERNAME):
        create_user(PREMIUM_DEMO_USERNAME, PREMIUM_DEMO_PASSWORD)
    demo_user, _ = authenticate(PREMIUM_DEMO_USERNAME, PREMIUM_DEMO_PASSWORD)
    if demo_user and not is_premium(demo_user["id"]):
        set_premium(demo_user["id"], True)


seed_premium_demo_account()


def _solid_sphere_svg(parts, defs, grad_id, cx, cy, r, base_hex, highlight_hex, label=""):
    """Appends a 'solid' glossy sphere (radial-gradient shaded circle, like a
    tiny 3D planet) plus an optional label to parts/defs — pure SVG, no
    external images, so it always renders identically everywhere."""
    defs.append(
        f'<radialGradient id="{grad_id}" cx="35%" cy="30%" r="75%">'
        f'<stop offset="0%" stop-color="{highlight_hex}"/>'
        f'<stop offset="55%" stop-color="{base_hex}"/>'
        f'<stop offset="100%" stop-color="{base_hex}" stop-opacity="0.85"/>'
        f'</radialGradient>'
    )
    parts.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r}" fill="url(#{grad_id})" '
                 f'stroke="rgba(0,0,0,0.15)" stroke-width="0.6"/>')
    if label:
        parts.append(f'<text x="{cx:.1f}" y="{cy:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="{r*1.05:.1f}" font-weight="700" fill="#ffffff" '
                      f'font-family="Georgia, serif" opacity="0.97" '
                      f'style="paint-order:stroke;stroke:rgba(0,0,0,0.25);stroke-width:{r*0.12:.2f}px;">'
                      f'{label}</text>')


# ---- Poster planet colours (base, highlight), matched to the provided
# design's exact gradients, reused via the existing _solid_sphere_svg helper.
POSTER_PLANET_COLORS = {
    "Su": ("#E74C3C", "#FFADA0"), "Mo": ("#D8D8D8", "#FFFFFF"),
    "Ma": ("#E74C3C", "#FF9E8F"), "Me": ("#2ECC71", "#B8F5D0"),
    "Jp": ("#F1C40F", "#FFF3B0"), "Ve": ("#F1948A", "#FFD9D4"),
    "Sa": ("#8B5E3C", "#D8B98A"), "Ra": ("#8E44AD", "#D8B8E8"),
    "Ke": ("#95A5A6", "#E0E5E5"),
}
POSTER_PLANET_NAMES = {
    "Su": "Sun", "Mo": "Moon", "Ma": "Mars", "Me": "Mercury", "Jp": "Jupiter",
    "Ve": "Venus", "Sa": "Saturn", "Ra": "Rahu", "Ke": "Ketu",
}
# (key, radius_fraction_of_canvas, angle_degrees, size_fraction, has_rings)
POSTER_PLANET_LAYOUT = [
    ("Su", 0.290, 122.4, 0.115, False),
    ("Mo", 0.275, 289.1, 0.065, False),
    ("Ma", 0.238, 71.5, 0.068, False),
    ("Me", 0.239, 253.4, 0.062, False),
    ("Jp", 0.324, 210.0, 0.135, False),
    ("Ve", 0.341, 164.2, 0.085, False),
    ("Sa", 0.340, 341.7, 0.098, True),
    ("Ra", 0.398, 25.0, 0.075, False),
    ("Ke", 0.238, 29.5, 0.063, False),
]


def build_planetspath_solar_svg(size: int = 760) -> str:
    """A single self-contained SVG: the golden Om medallion sits at the exact
    centre, with all nine grahas placed on real circular orbit paths around
    it (three concentric radii) — deliberately one SVG rather than a stack of
    absolutely-positioned CSS divs, since that's what produced the layout bug
    where the previous version rendered full-width above the page instead of
    staying inside its column."""
    cx = cy = size / 2
    defs = []
    parts = [f'<svg viewBox="0 0 {size} {size}" width="{size}" height="{size}" '
             f'xmlns="http://www.w3.org/2000/svg" style="display:block;max-width:100%;">']

    def pt(r, deg):
        rad = math.radians(deg - 90)
        return cx + r * math.cos(rad), cy + r * math.sin(rad)

    defs.append(
        '<radialGradient id="ppOmGlow" cx="50%" cy="50%" r="55%">'
        '<stop offset="0%" stop-color="#FFF6D8" stop-opacity="0.9"/>'
        '<stop offset="70%" stop-color="#FFE9A8" stop-opacity="0.3"/>'
        '<stop offset="100%" stop-color="#FFE9A8" stop-opacity="0"/></radialGradient>'
    )
    defs.append(
        '<linearGradient id="ppOmGold" x1="0%" y1="0%" x2="100%" y2="100%">'
        '<stop offset="0%" stop-color="#F5C244"/>'
        '<stop offset="50%" stop-color="#C9910E"/>'
        '<stop offset="100%" stop-color="#8B6508"/></linearGradient>'
    )
    defs.append(
        '<filter id="ppOmShadow" x="-40%" y="-40%" width="180%" height="180%">'
        '<feDropShadow dx="1.5" dy="2.5" stdDeviation="1.3" flood-color="#5C3A00" flood-opacity="0.45"/>'
        '</filter>'
    )
    for r_frac in (0.30, 0.44):
        parts.append(f'<circle cx="{cx}" cy="{cy}" r="{size*r_frac:.1f}" fill="none" stroke="#D8A845" '
                      f'stroke-width="1" stroke-dasharray="2,9" opacity="0.4"/>')

    parts.append(f'<circle cx="{cx}" cy="{cy}" r="{size*0.23:.1f}" fill="url(#ppOmGlow)"/>')
    parts.append(f'<circle cx="{cx}" cy="{cy}" r="{size*0.16:.1f}" fill="#FFFDF3" stroke="#B8842E" stroke-width="3"/>')
    OM_FONTS = ("'Noto Sans Devanagari','Nirmala UI','Kohinoor Devanagari',"
                "'Devanagari Sangam MN','Mangal',sans-serif")
    parts.append(f'<text x="{cx}" y="{cy}" text-anchor="middle" dominant-baseline="central" '
                 f'font-size="{size*0.17:.1f}" fill="url(#ppOmGold)" font-family="{OM_FONTS}" '
                 f'filter="url(#ppOmShadow)">\u0950</text>')
    sx, sy = pt(size * 0.19, 0)
    parts.append(f'<text x="{sx:.1f}" y="{sy:.1f}" text-anchor="middle" font-size="22" fill="#dfa72f">\u2726</text>')
    sx2, sy2 = pt(size * 0.19, 180)
    parts.append(f'<text x="{sx2:.1f}" y="{sy2:.1f}" text-anchor="middle" font-size="22" fill="#dfa72f">\u2726</text>')

    for key, r_frac, angle, sz_frac, has_rings in POSTER_PLANET_LAYOUT:
        px, py = pt(size * r_frac, angle)
        r = size * sz_frac
        base_hex, hi_hex = POSTER_PLANET_COLORS[key]
        if key == "Su":
            defs.append(
                '<radialGradient id="ppSunFlare" cx="50%" cy="50%" r="60%">'
                '<stop offset="0%" stop-color="#FFB3A0" stop-opacity="0.9"/>'
                '<stop offset="60%" stop-color="#F5745C" stop-opacity="0.25"/>'
                '<stop offset="100%" stop-color="#F5745C" stop-opacity="0"/></radialGradient>'
            )
            parts.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="{r*2.1:.1f}" fill="url(#ppSunFlare)"/>')
        if has_rings:
            parts.append(f'<ellipse cx="{px:.1f}" cy="{py:.1f}" rx="{r*1.7:.1f}" ry="{r*0.5:.1f}" '
                          f'fill="none" stroke="#B8842E" stroke-width="{r*0.12:.1f}" opacity="0.6" '
                          f'transform="rotate(-18 {px:.1f} {py:.1f})"/>')
        _solid_sphere_svg(parts, defs, f"ppSph_{key}", px, py, r, base_hex, hi_hex)
        label_text = POSTER_PLANET_NAMES[key]
        label_w = len(label_text) * 7.0 + 20
        points_left = px < cx
        if points_left:
            label_x = px - r - 8 - label_w
            dot_x, text_x, text_anchor = label_x + label_w - 10, label_x + label_w - 18, "end"
        else:
            label_x = px + r + 8
            dot_x, text_x, text_anchor = label_x + 10, label_x + 18, "start"
        parts.append(f'<rect x="{label_x:.1f}" y="{py-10:.1f}" width="{label_w:.1f}" height="20" rx="10" '
                      f'fill="#FFFDF3" stroke="#F0DE94" stroke-width="1" opacity="0.95"/>')
        parts.append(f'<circle cx="{dot_x:.1f}" cy="{py:.1f}" r="2.5" fill="{base_hex}"/>')
        parts.append(f'<text x="{text_x:.1f}" y="{py:.1f}" dominant-baseline="middle" text-anchor="{text_anchor}" '
                      f'font-size="11.5" fill="#3A2E1F" font-family="Georgia, serif">{label_text}</text>')

    svg_open = parts[0]
    body = "".join(parts[1:])
    return svg_open + "<defs>" + "".join(defs) + "</defs>" + body + "</svg>"


def render_planetspath_solar_with_features():
    """One integrated composition: the solar system SVG sits in the center of
    a 3x3 layout, with all 8 FEATURE_STRIP items filling the surrounding
    cells — 8 features fits a 3x3 grid minus its center perfectly. Built as
    an HTML table rather than CSS Grid: table layout is universally
    supported (works identically in every browser, old or new), whereas
    grid-template-areas support couldn't be verified from this environment's
    rendering tools. Replaces the old layout of a solar graphic with a
    separate feature row below it, which left the space around the planets
    empty. No chevron arrows — these are informational, not links."""
    solar_svg = build_planetspath_solar_svg(620)

    def _cell(icon, title, desc, section_id, valign="top"):
        inner = (
            f'<div class="pp-mini-feature{" pp-mini-clickable" if section_id else ""}">'
            f'<div class="pp-mini-icon">{icon}</div>'
            f'<div><div class="pp-mini-title">{title.upper()}</div>'
            f'<div class="pp-mini-text">{desc}</div></div></div>'
        )
        if section_id:
            inner = f'<a href="?goto={section_id}" target="_self" style="text-decoration:none;color:inherit;">{inner}</a>'
        return f'<td class="pp-grid-cell" style="vertical-align:{valign};">{inner}</td>'

    f = FEATURE_STRIP
    rows_html = (
        f'<tr>{_cell(*f[0])}{_cell(*f[1])}{_cell(*f[2])}</tr>'
        f'<tr>{_cell(*f[3], valign="middle")}'
        f'<td class="pp-grid-cell pp-center-cell" style="text-align:center;vertical-align:middle;padding:0;">'
        f'<div class="pp-mini-solar">{solar_svg}</div></td>'
        f'{_cell(*f[4], valign="middle")}</tr>'
        f'<tr>{_cell(*f[5])}{_cell(*f[6])}{_cell(*f[7])}</tr>'
    )
    st.markdown(
        f"""
        <style>
        .pp-solar-table {{ width:100%; border-collapse:separate; border-spacing:12px 10px; table-layout:fixed; margin-top:6px; }}
        .pp-grid-cell {{ width:27%; }}
        .pp-center-cell {{ width:46%; }}
        .pp-mini-feature {{
            background:rgba(255,255,255,.92); border:1px solid #eadfca; border-radius:16px;
            padding:16px 18px; display:flex; align-items:center; gap:14px;
            box-shadow:0 2px 8px rgba(104,82,40,.06); min-height:96px;
            transition: box-shadow 0.15s, border-color 0.15s, transform 0.15s;
        }}
        .pp-mini-clickable:hover {{
            box-shadow:0 6px 16px rgba(104,82,40,.14); border-color:#d8a845; transform:translateY(-2px);
        }}
        .pp-mini-solar {{ width:300px; height:300px; margin:0 auto; }}
        .pp-mini-solar svg {{ width:300px !important; height:300px !important; }}
        .pp-mini-icon {{
            width:50px; height:50px; border:1px solid #e8bd65; border-radius:50%;
            display:flex; align-items:center; justify-content:center; font-size:23px; color:#d28c16;
            flex-shrink:0; background:linear-gradient(145deg,#fff,#fffaf0);
        }}
        .pp-mini-title {{ color:#1b3158; font-weight:700; font-size:16px; letter-spacing:0.01em; margin-bottom:5px; }}
        .pp-mini-text {{ color:#59657a; font-size:13.5px; line-height:1.4; }}
        </style>
        <table class="pp-solar-table"><tbody>{rows_html}</tbody></table>
        """,
        unsafe_allow_html=True,
    )
    st.markdown(
        '<div class="pp-trust" style="margin-top:10px;">\u2699 Accurate Calculations <span>\u2022</span> '
        '\u2726 Real Astronomy Data <span>\u2022</span> \u25c8 Trusted Insights</div>',
        unsafe_allow_html=True,
    )


FEATURE_STRIP = [
    ("\u25c8", "Kundali Analysis", "Detailed insights from your real birth chart", None),
    ("\U0001f504", "Nakshatra Live & Transits", "Today's tithi, nakshatra, and live planetary positions", "section-transit"),
    ("\U0001f4ff", "Day-wise Remedies", "Gemstones, colours & practices for each weekday", "section-remedies"),
    ("\U0001f319", "Navtara Chakra", "Auspicious-day calendar based on your own nakshatra", "section-navtara"),
    ("\U0001f549\ufe0f", "Panchang & Muhurta", "Daily panchang, hora timings, and auspicious windows", "section-muhurta"),
    ("\U0001f49e", "Compatibility", "Match your kundali against a partner's, graha by graha", "section-compat"),
    ("\U0001f4c1", "Charts", "Save, revisit, and manage your birth charts", "section-charts"),
    ("\U0001f522", "Numerology", "Life Path, Destiny, Soul Urge — Pythagorean and Chaldean", "section-numerology"),
]


def build_compass_star_svg(size: int = 90) -> str:
    """Small decorative compass-star mark used above the brand wordmark."""
    cx = cy = size / 2
    r_out, r_in = size * 0.46, size * 0.16
    pts = []
    for i in range(16):
        ang = math.radians(i * 22.5 - 90)
        r = r_out if i % 2 == 0 else r_out * 0.42
        pts.append(f"{cx + r*math.cos(ang):.1f},{cy + r*math.sin(ang):.1f}")
    return (
        f'<svg viewBox="0 0 {size} {size}" xmlns="http://www.w3.org/2000/svg" style="display:block;margin:0 auto;">'
        f'<circle cx="{cx}" cy="{cy}" r="{r_out+8}" fill="none" stroke="#d79a1e" stroke-width="1.5" opacity="0.6"/>'
        f'<polygon points="{" ".join(pts)}" fill="none" stroke="#d79a1e" stroke-width="2"/>'
        f'<circle cx="{cx}" cy="{cy}" r="{r_in*0.5}" fill="#d79a1e"/>'
        f'</svg>'
    )


def render_auth_screen():
    """Full-page login / signup flow. Returns nothing — sets
    st.session_state['user'] and reruns once authenticated."""
    NAVY = "#162b51"
    GOLD = "#c98b17"

    st.markdown(
        f"""
        <style>
        .stApp {{
            background:
                radial-gradient(circle at 75% 35%, rgba(255,225,140,.22), transparent 28%),
                radial-gradient(circle at 20% 75%, rgba(255,215,120,.13), transparent 30%),
                linear-gradient(135deg,#ffffff 0%,#fffdf8 48%,#fff8e9 100%) !important;
            background-attachment: fixed;
        }}
        .block-container {{ padding-top: 1rem !important; }}
        .pp-header {{ display:flex; align-items:center; gap:16px; padding:10px 4px 14px;
            border-bottom:1px solid #eee6d7; margin-bottom:16px; }}
        .pp-brand-name {{ color:#714d14; font-size:52px; font-weight:bold; letter-spacing:-1px;
            font-family:Georgia,serif; white-space:nowrap; line-height:1.1; }}
        .pp-tagline {{ font-family:Arial,sans-serif; font-size:11px; letter-spacing:4px; color:#52617a; margin-top:4px; }}
        .hero-headline {{ color:{NAVY}; font-family:Georgia,serif; font-size:30px; line-height:1.15;
            margin:4px 0 8px; }}
        .hero-headline .accent {{ color:{GOLD}; }}
        .hero-desc {{ font-family:Arial,sans-serif; color:#59647a; font-size:14px; line-height:1.55;
            max-width:430px; margin-bottom:21px; }}
        .welcome-back {{ text-align:center; font-size:19px; color:#bd7e13; font-family:Georgia,serif;
            margin:2px 0 10px; }}
        .welcome-back:before, .welcome-back:after {{ content:"\u2727"; margin:0 14px; color:#e1a63a; }}
        div[data-testid="stTabs"] {{
            background: rgba(255,255,255,.92); border:1px solid #eee0c6; border-radius:22px;
            padding:12px 25px 18px;
            box-shadow: 0 15px 35px rgba(117,88,28,.10), 0 3px 8px rgba(117,88,28,.05);
            max-width:410px;
        }}
        div[data-testid="stTabs"] button[role="tab"] {{ font-weight:700; letter-spacing:0.03em; color:#697083; }}
        div[data-testid="stTabs"] button[role="tab"][aria-selected="true"] {{ color:{GOLD}; }}
        div[data-testid="stTabs"] .stButton button {{
            background: linear-gradient(90deg,#f5c85d,#dd9014) !important; color:#fff !important;
            border:none !important; font-family:Georgia,serif; font-size:17px; font-weight:700;
            border-radius:8px !important; box-shadow:0 4px 10px rgba(210,145,29,.2);
        }}
        .pp-forgot {{ text-align:center; color:#47526a; font-family:Arial,sans-serif; font-size:13px;
            padding-top:10px; }}
        .pp-features {{ background:rgba(255,255,255,.93); border:1px solid #eadfca; border-radius:22px;
            box-shadow: 0 12px 30px rgba(104,82,40,.09), 0 2px 7px rgba(104,82,40,.04);
            overflow:hidden; margin:30px 0 18px; }}
        .pp-feature-row {{ display:grid; grid-template-columns:repeat(4,1fr); }}
        .pp-feature {{ display:flex; align-items:center; padding:16px 22px; border-right:1px solid #eee9df;
            border-bottom:1px solid #eee9df; }}
        .pp-feature:nth-child(4n) {{ border-right:0; }}
        .pp-feature-icon {{ width:58px; height:58px; border:1px solid #e8bd65; border-radius:50%;
            display:flex; align-items:center; justify-content:center; font-size:25px; color:#d28c16;
            margin-right:13px; flex-shrink:0; background:linear-gradient(145deg,#fff,#fffaf0);
            box-shadow:0 3px 9px rgba(201,143,37,.10); }}
        .pp-feature-title {{ color:#1b3158; font-weight:bold; font-size:15px; margin-bottom:5px; }}
        .pp-feature-text {{ font-family:Arial,sans-serif; color:#59657a; font-size:12px; line-height:1.4; }}
        .pp-feature-arrow {{ color:#d28b16; font-size:23px; margin-left:8px; }}
        .pp-trust {{ text-align:center; border:1px solid #e5dccb; background:rgba(255,255,255,.84);
            border-radius:25px; padding:10px 28px; font-size:13px; color:#233a60; margin:0 auto 20px;
            max-width:560px; }}
        .pp-trust span {{ margin:0 13px; color:#cf8b17; }}
        </style>
        """,
        unsafe_allow_html=True,
    )

    st.markdown(
        f'<div class="pp-header">'
        f'<div style="max-width:66px;">{build_compass_star_svg(66)}</div>'
        f'<div><div class="pp-brand-name">PlanetsPath</div>'
        f'<div class="pp-tagline">DISCOVER &nbsp;\u2022&nbsp; REFLECT &nbsp;\u2022&nbsp; GROW</div></div>'
        f'</div>',
        unsafe_allow_html=True,
    )

    hero_l, hero_r = st.columns([1, 1.1])

    with hero_l:
        st.markdown(
            '<p class="hero-headline">Your <span class="accent">Birth</span> Chart Awaits</p>',
            unsafe_allow_html=True,
        )
        st.markdown(
            '<p class="hero-desc">Explore Vedic astrology, nakṣatras, divisional charts, live '
            'planetary transits, and more — every calculation powered by real astronomy.</p>',
            unsafe_allow_html=True,
        )
        st.markdown('<p class="welcome-back">Welcome Back</p>', unsafe_allow_html=True)

        tab_login, tab_signup = st.tabs(["SIGN IN", "NEW SIGN UP"])

        with tab_login:
            identifier = st.text_input("Username", key="login_identifier", placeholder="User Name")
            password = st.text_input("Password", type="password", key="login_password", placeholder="Password")
            remember_me = st.checkbox("Remember me", value=True, key="login_remember_me")
            if st.button("Sign In  \u2192", use_container_width=True, key="signin_btn"):
                if not identifier or not password:
                    st.error("Enter your username and password.")
                else:
                    user, msg = authenticate(identifier.strip(), password)
                    if user:
                        st.session_state["user"] = {"id": user["id"], "username": user["username"]}
                        if remember_me:
                            raw_token = create_remember_token(user["id"])
                            st.query_params["rt"] = raw_token
                        st.rerun()
                    else:
                        st.error(msg)
            st.markdown('<p class="pp-forgot">Forgot Password?</p>', unsafe_allow_html=True)

        with tab_signup:
            su_username = st.text_input("Username (3-20 letters/numbers/underscore)", key="su_username")
            su_email = st.text_input("Email (enter this or phone number below)", key="su_email", placeholder="you@example.com")
            su_phone = st.text_input("Phone number (enter this or email above)", key="su_phone", placeholder="+91 98765 43210")
            su_pw = st.text_input("Password (min 8 characters)", type="password", key="su_pw")
            su_pw2 = st.text_input("Confirm password", type="password", key="su_pw2")
            su_terms = st.checkbox("I agree to the Terms of Service and Privacy Policy", key="su_terms")
            if st.button("Create account", use_container_width=True, key="signup_btn"):
                errors = []
                if not USERNAME_RE.match(su_username or ""):
                    errors.append("Username must be 3-20 characters: letters, numbers, underscore only.")
                elif username_taken(su_username):
                    errors.append("That username is already taken — pick another one.")
                su_email_clean = (su_email or "").strip()
                if su_email_clean:
                    if not EMAIL_RE.match(su_email_clean):
                        errors.append("Enter a valid email address, or leave it blank.")
                    elif email_taken(su_email_clean):
                        errors.append("That email is already registered — try logging in instead.")
                su_phone_clean = re.sub(r"[\s\-()]", "", (su_phone or "").strip())
                if su_phone_clean:
                    if not PHONE_RE.match(su_phone_clean):
                        errors.append("Enter a valid phone number (7-15 digits, optional + prefix), or leave it blank.")
                    elif phone_taken(su_phone_clean):
                        errors.append("That phone number is already registered — try logging in instead.")
                if not su_email_clean and not su_phone_clean:
                    errors.append("Enter at least one of Email or Phone number.")
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
                    ok, msg = create_user(su_username.strip(), su_pw, su_email_clean, su_phone_clean)
                    if not ok:
                        st.error(msg)
                    else:
                        st.success("Account created — you can sign in now.")

    with hero_r:
        render_planetspath_solar_with_features()


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

# ---- Nakshatra ruling deity & symbol (classical, index-matched to NAKSHATRAS) ----
NAKSHATRA_DEITY_ASCII = [
    "Ashwini Kumaras", "Yama", "Agni", "Brahma", "Soma (Moon)", "Rudra", "Aditi",
    "Brihaspati", "Nagas (serpents)", "Pitrs (ancestors)", "Bhaga", "Aryaman",
    "Savitar", "Tvashtar (Vishwakarma)", "Vayu", "Indra-Agni", "Mitra", "Indra",
    "Nirriti", "Apas (waters)", "Vishvadevas", "Vishnu", "Vasus (eight)", "Varuna",
    "Aja Ekapada", "Ahir Budhnya", "Pushan",
]
NAKSHATRA_SYMBOL_ASCII = [
    "Horse's head", "Yoni", "Razor / axe", "Chariot / cart", "Deer's head",
    "Teardrop / gem", "Bow and quiver", "Cow's udder", "Coiled serpent",
    "Royal throne", "Front legs of a bed", "Back legs of a bed", "Hand / fist",
    "Bright jewel", "Young shoot / coral", "Triumphal archway", "Lotus",
    "Circular amulet", "Bunch of roots", "Elephant tusk (front)",
    "Elephant tusk (back)", "Ear / three footprints", "Drum", "Empty circle",
    "Sword / front funeral cot", "Back of funeral cot", "Fish / drum",
]

# ---- Graha Maitri: classical Naisargika (natural, fixed) planetary friendship,
# as given in Brihat Parashara Hora Shastra. Rahu/Ketu are shadow points and
# aren't part of this classical five-fold-relationship scheme.
GRAHA_MAITRI = {
    "Su": {"friends": ["Mo", "Ma", "Jp"], "enemies": ["Ve", "Sa"], "neutral": ["Me"]},
    "Mo": {"friends": ["Su", "Me"], "enemies": [], "neutral": ["Ma", "Jp", "Ve", "Sa"]},
    "Ma": {"friends": ["Su", "Mo", "Jp"], "enemies": ["Me"], "neutral": ["Ve", "Sa"]},
    "Me": {"friends": ["Su", "Ve"], "enemies": ["Mo"], "neutral": ["Ma", "Jp", "Sa"]},
    "Jp": {"friends": ["Su", "Mo", "Ma"], "enemies": ["Me", "Ve"], "neutral": ["Sa"]},
    "Ve": {"friends": ["Me", "Sa"], "enemies": ["Su", "Mo"], "neutral": ["Ma", "Jp"]},
    "Sa": {"friends": ["Me", "Ve"], "enemies": ["Su", "Mo", "Ma"], "neutral": ["Jp"]},
}

# ---- Planetary dignity: exaltation / debilitation / own sign (classical, fixed).
# Rahu/Ketu exaltation-debilitation varies by text; using the commonly cited
# Parashari convention (Rahu: Taurus/Scorpio, Ketu: Scorpio/Taurus).
EXALTATION_SIGN = {"Su": 0, "Mo": 1, "Ma": 9, "Me": 5, "Jp": 3, "Ve": 11, "Sa": 6, "Ra": 1, "Ke": 7}
DEBILITATION_SIGN = {"Su": 6, "Mo": 7, "Ma": 3, "Me": 11, "Jp": 9, "Ve": 5, "Sa": 0, "Ra": 7, "Ke": 1}
OWN_SIGNS = {"Su": {4}, "Mo": {3}, "Ma": {0, 7}, "Me": {2, 5}, "Jp": {8, 11}, "Ve": {1, 6}, "Sa": {9, 10}}


def graha_dignity(key: str, sign: int) -> str:
    if EXALTATION_SIGN.get(key) == sign:
        return "Exalted"
    if DEBILITATION_SIGN.get(key) == sign:
        return "Debilitated"
    if sign in OWN_SIGNS.get(key, set()):
        return "Own Sign"
    return "Neutral"


# ============================================================
# TRANSIT INSIGHTS — general educational context for the Current Transit
# table, NOT personalized predictions. Combines: (1) what this graha's
# transits generally influence, (2) how its current sign-dignity colours
# that, (3) the nakshatra's classical deity/symbol flavour, and (4) any
# other grahas currently conjunct (sharing the same sign) it right now.
# ============================================================

GRAHA_TRANSIT_THEME = {
    "Su": "The Sun's transits generally highlight vitality, self-expression, authority, "
          "recognition, and how confidently you present yourself to the world.",
    "Mo": "The Moon moves fastest of all — its transits colour the emotional tone, mind, "
          "instincts, and domestic/comfort matters of roughly two and a half days at a time.",
    "Ma": "Mars's transits generally influence energy, drive, courage, conflict, and "
          "how assertively action gets taken during this period.",
    "Me": "Mercury's transits generally shape communication, intellect, commerce, travel, "
          "and how clearly (or not) ideas and information move during this period.",
    "Jp": "Jupiter's transits generally bring expansion, growth, opportunity, wisdom, and "
          "optimism to whatever area of life it's currently touching.",
    "Ve": "Venus's transits generally influence relationships, aesthetics, comfort, finances, "
          "and harmony (or friction) in matters of love and pleasure.",
    "Sa": "Saturn's transits generally bring discipline, structure, delay, and long-term "
          "consequence — themes that build slowly rather than arriving quickly.",
    "Ra": "Rahu's transits generally amplify ambition, unconventional paths, obsession, and "
          "a hunger for things outside one's usual comfort zone.",
    "Ke": "Ketu's transits generally bring detachment, introspection, and a pull away from "
          "material engagement toward spiritual or inward-facing themes.",
}

DIGNITY_EFFECT_NOTE = {
    "Exalted": "It's currently exalted here — classically its strongest possible placement, "
               "so its themes tend to express in an amplified, confident, favourable way.",
    "Own Sign": "It's currently in its own sign — a stable, comfortable placement where it "
                "tends to express its themes steadily and with self-assurance.",
    "Neutral": "It's currently in a sign that's neither especially strong nor weak for it — "
               "effects tend to be moderate and more dependent on other chart factors.",
    "Debilitated": "It's currently debilitated here — classically its most challenged "
                   "placement, so its themes may express with more friction or require "
                   "extra conscious effort to work well.",
}


def compute_transit_conjunctions(transit_bodies: list) -> dict:
    """For each graha, returns the list of other graha keys currently sharing
    its sign (a real, directly-computable technique — Graha Yuti/conjunction —
    as opposed to the more speculative parts of transit reading)."""
    by_sign = {}
    for b in transit_bodies:
        if b["key"] == "As":
            continue
        by_sign.setdefault(b["sign"], []).append(b["key"])
    result = {}
    for b in transit_bodies:
        if b["key"] == "As":
            continue
        others = [k for k in by_sign.get(b["sign"], []) if k != b["key"]]
        result[b["key"]] = others
    return result


def build_transit_insight(b: dict, conjunctions: list) -> str:
    """Combines theme + dignity + nakshatra flavour + conjunctions into one
    short educational paragraph for a single graha's current transit."""
    key, sign, nak_idx = b["key"], b["sign"], b["nakIdx"]
    dignity = graha_dignity(key, sign)
    parts = [GRAHA_TRANSIT_THEME[key], DIGNITY_EFFECT_NOTE[dignity]]
    parts.append(
        f"Its current nakshatra, {NAKSHATRAS_ASCII[nak_idx]}, carries the classical flavour "
        f"of {NAKSHATRA_DEITY_ASCII[nak_idx]} and is symbolised by the {NAKSHATRA_SYMBOL_ASCII[nak_idx]} — "
        f"a subtle undertone on top of the sign-level theme above."
    )
    if conjunctions:
        names = ", ".join(BODY_FULLNAME_ASCII.get(k, k) for k in conjunctions)
        parts.append(
            f"It's also currently conjunct (sharing the same sign as) {names} — when grahas "
            f"transit together like this, their themes tend to blend and interact rather than "
            f"play out independently."
        )
    else:
        parts.append("No other graha currently shares its sign, so its themes are playing out "
                      "on their own right now rather than blending with another planet's.")
    return " ".join(parts)


def nakshatra_lord_relationship_note(graha_key: str, nak_idx: int) -> str:
    """Classical technique: a graha's nakshatra placement reads more supportive when
    the nakshatra's ruling lord (from the Vimshottari 9-lord cycle) is a natural
    friend of that graha, and more challenging when it's a natural enemy - using
    the same Graha Maitri table as the Planetary Friendship section."""
    lord_key = DASHA_LORD_SHORT[nak_idx % 9]
    if graha_key in ("Ra", "Ke"):
        return ("Rahu/Ketu are shadow points outside the classical friendship scheme "
                "- read this placement via the sign's dispositor instead.")
    if lord_key == graha_key:
        return "Own nakshatra (ruled by itself) - a strong, self-supporting placement."
    if lord_key in ("Ra", "Ke"):
        return (f"Nakshatra lord ({BODY_FULLNAME_ASCII[lord_key]}) is a shadow point "
                "outside the classical friendship scheme - a more unpredictable placement.")
    rel = GRAHA_MAITRI.get(graha_key)
    if not rel:
        return "-"
    lord_name = BODY_FULLNAME_ASCII[lord_key]
    if lord_key in rel["friends"]:
        return f"Nakshatra lord {lord_name} is a natural friend - generally supportive, smoother results."
    if lord_key in rel["enemies"]:
        return f"Nakshatra lord {lord_name} is a natural enemy - more friction, mixed or delayed results."
    return f"Nakshatra lord {lord_name} is neutral - moderate effect, depends on other chart factors."


# ---- Day-wise remedies: classical, general associations by weekday/ruling
# planet. General traditional information, not a personalized prescription —
# gemstones in particular should only be worn after a proper chart analysis,
# since an unsuitable one can do more harm than good for some charts.
DAY_REMEDIES = [
    ("Sunday", "Su", "Ruby", "Red", "Offer water to the rising Sun; recite the Āditya Hṛdayam"),
    ("Monday", "Mo", "Pearl", "White", "Offer milk to Śiva; chant the Candra mantra"),
    ("Tuesday", "Ma", "Red Coral", "Red", "Recite the Hanumān Cālīsā; donate red lentils"),
    ("Wednesday", "Me", "Emerald", "Green", "Feed green gram to birds or cows; chant Viṣṇu Sahasranāma"),
    ("Thursday", "Jp", "Yellow Sapphire", "Yellow", "Worship Viṣṇu/Guru; donate turmeric or chana dal"),
    ("Friday", "Ve", "Diamond / White Sapphire", "White", "Worship Goddess Lakṣmī; donate white items"),
    ("Saturday", "Sa", "Blue Sapphire", "Black / Blue", "Recite the Śani mantra; donate mustard oil or black til"),
]


NAVAGRAHA_ORDER = ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa", "Ra", "Ke"]
NAVAGRAHA_FULLNAME = {
    "Su": "Sūrya", "Mo": "Candra", "Ma": "Maṅgala", "Me": "Budha", "Jp": "Guru",
    "Ve": "Śukra", "Sa": "Śani", "Ra": "Rāhu", "Ke": "Ketu",
}
DIGNITY_COLOR_KEY = {"Exalted": "gold", "Debilitated": "muted", "Own Sign": "sindoor", "Neutral": "ivory"}


def build_navagraha_wheel_svg(birth_bodies) -> str:
    """A dedicated circular diagram of just the 9 grahas (fixed order, not tied
    to zodiacal position), color-coded by classical dignity — exalted, own
    sign, debilitated, or neutral — for an at-a-glance strength overview."""
    cx, cy = 300, 300
    R_outer, R_mid, R_inner = 280, 200, 60
    n = len(NAVAGRAHA_ORDER)
    seg = 360 / n
    body_by_key = {b["key"]: b for b in birth_bodies}

    parts = [
        f'<svg viewBox="0 0 {2*cx} {2*cy}" width="600" height="600" '
        'xmlns="http://www.w3.org/2000/svg" style="display:block;">',
        '<defs><radialGradient id="navwheel" cx="50%" cy="50%" r="70%">'
        '<stop offset="0%" stop-color="#FFFDE7" /><stop offset="100%" stop-color="#FFF3B0" />'
        '</radialGradient></defs>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_outer}" fill="url(#navwheel)" stroke="{C["gold"]}" stroke-width="2"/>',
        f'<circle cx="{cx}" cy="{cy}" r="{R_mid}" fill="none" stroke="{C["line"]}" stroke-width="1"/>',
    ]

    for i, key in enumerate(NAVAGRAHA_ORDER):
        boundary = i * seg - seg / 2
        x1, y1 = _wheel_point(cx, cy, R_inner, boundary)
        x2, y2 = _wheel_point(cx, cy, R_outer, boundary)
        parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                      f'stroke="{C["line"]}" stroke-width="1"/>')

        center_angle = i * seg
        b = body_by_key.get(key)
        if b is None:
            continue
        dignity = graha_dignity(key, b["sign"])
        fill = C[DIGNITY_COLOR_KEY[dignity]]
        retro = "℞" if (b["retro"] and key not in ("Ra", "Ke")) else ""

        lx, ly = _wheel_point(cx, cy, (R_outer + R_mid) / 2, center_angle)
        parts.append(f'<text x="{lx:.1f}" y="{ly-8:.1f}" text-anchor="middle" font-size="15" '
                      f'font-weight="700" fill="{fill}" font-family="Georgia, serif">{NAVAGRAHA_FULLNAME[key]}</text>')
        parts.append(f'<text x="{lx:.1f}" y="{ly+8:.1f}" text-anchor="middle" font-size="11" '
                      f'fill="{C["muted"]}" font-family="monospace">{SIGN_ABBR[b["sign"]]} {math.floor(b["inSign"])}°{retro}</text>')
        parts.append(f'<text x="{lx:.1f}" y="{ly+22:.1f}" text-anchor="middle" font-size="9" '
                      f'fill="{fill}" font-family="Georgia, serif">{dignity}</text>')

        mx, my = _wheel_point(cx, cy, (R_mid + R_inner) / 2, center_angle)
        parts.append(f'<text x="{mx:.1f}" y="{my:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="9" fill="{C["muted"]}" font-family="monospace">{NAK_ABBR[b["nakIdx"]]}</text>')

    parts.append(f'<circle cx="{cx}" cy="{cy}" r="{R_inner}" fill="{C["panel"]}" stroke="{C["gold"]}" stroke-width="1.5"/>')
    parts.append(f'<text x="{cx}" y="{cy}" text-anchor="middle" dominant-baseline="middle" '
                 f'font-size="16" font-weight="700" fill="{C["gold"]}" font-family="Georgia, serif">Navagraha</text>')
    parts.append("</svg>")
    return "".join(parts)


# ============================================================
# NAVTARA CHAKRA — nine-tara auspiciousness calendar
# ============================================================
# Ported from a standalone Flask tool. That version used average lunar
# periods anchored to a single reference date to project nakshatra/tithi
# for any day — a reasonable approximation, but one that drifts and needs
# re-anchoring occasionally. This app already has a real ephemeris (the
# same Sun/Moon longitude + ayanamsa math used everywhere else here), so
# every date below is computed directly instead of projected — the
# curated tara descriptions (meaning/significance/dos/avoids/tip) are
# unchanged from the original.

NAVTARA_INFO = [
    dict(name="Janma", good=False, bg="#F7C1C1", fg="#501313",
         meaning="Your own nakshatra recurring every 27 days. Considered the mildest "
                 "of the four difficult taras, since it simply marks the day the moon "
                 "returns to your birth star.",
         significance="Rules the physical body and general life current. Not deeply "
                       "harmful, but not a day to push your luck either.",
         dos=["Routine chores and errands", "Self-care, rest", "Continuing existing work",
              "Worship or prayer tied to your own nakshatra"],
         avoids=["Launching new ventures", "Big financial commitments", "Important travel"],
         tip="If something is unavoidable today, check the hourly choghadiya for a "
             "favorable window rather than skipping the day entirely."),
    dict(name="Sampat", good=True, bg="#97C459", fg="#173404",
         meaning="Counted 2nd from janma. Governs gain, prosperity, and the "
                 "accumulation of resources.",
         significance="One of the four classically auspicious taras. Energy tends to "
                       "flow toward growth and accumulation.",
         dos=["Buying property or gold", "Starting a business", "Signing financial deals",
              "Investments", "Opening accounts"],
         avoids=["Nothing specific, but avoid pure speculation"],
         tip="Favored for anything where you want the outcome to multiply or compound "
             "over time."),
    dict(name="Vipat", good=False, bg="#E24B4A", fg="#ffffff",
         meaning="Counted 3rd from janma. Associated with risk, accidents, and "
                 "reversals of fortune.",
         significance="One of the four difficult taras and considered strongly "
                       "unfavorable, second only to Vadha in severity.",
         dos=["Cautious, low-stakes tasks", "Reviewing plans", "Indoor, low-risk work"],
         avoids=["Travel", "Medical procedures", "Signing contracts", "New beginnings",
                 "Adventurous activity"],
         tip="Best treated as a day to consolidate and double check, not to move forward."),
    dict(name="Kshema", good=True, bg="#C0DD97", fg="#173404",
         meaning="Counted 4th from janma. Governs safety, comfort, and steady wellbeing.",
         significance="A gentle, stabilizing auspicious tara, milder than Sampat or "
                       "Sadhaka but still favorable.",
         dos=["Health checkups or treatment", "Family functions", "Safe travel",
              "Moving house", "Routine wellbeing rituals"],
         avoids=["No major restriction"],
         tip="Good default choice when you just need a safe, uneventful day for "
             "something important."),
    dict(name="Pratyari", good=False, bg="#F09595", fg="#501313",
         meaning="Counted 5th from janma, also called Pratyak. Creates friction, "
                 "delay, and opposition from others.",
         significance="A moderately difficult tara: not as severe as Vipat or Vadha, "
                       "but prone to plans stalling midway.",
         dos=["Clearing pending, small tasks", "Patience-based work", "Internal planning"],
         avoids=["Starting projects", "Negotiations", "Travel", "Disputes or confrontations"],
         tip="If a meeting or negotiation is unavoidable, expect it to take longer "
             "than planned."),
    dict(name="Sadhaka", good=True, bg="#639922", fg="#ffffff",
         meaning="Counted 6th from janma. Governs the successful completion of effort "
                 "and intention.",
         significance="A strong auspicious tara, especially favored for anything "
                       "requiring focused effort toward a goal.",
         dos=["Important meetings", "Exams, study", "Spiritual practice", "Negotiations",
              "Skill-building"],
         avoids=["No major restriction"],
         tip="Considered one of the best days to start something that needs "
             "sustained follow-through."),
    dict(name="Vadha", good=False, bg="#A32D2D", fg="#ffffff",
         meaning="Counted 7th from janma, also called Naidhana. The most severe of "
                 "the nine taras.",
         significance="Classically the tara to avoid most. Associated with loss, "
                       "injury, or the collapse of plans.",
         dos=["Rest and quiet activity only"],
         avoids=["Marriage or ceremonies", "Surgery", "Signing contracts", "Travel",
                 "Any new beginning"],
         tip="Traditionally postponed rather than worked around. Wait for the next "
             "favorable tara if at all possible."),
    dict(name="Mitra", good=True, bg="#EAF3DE", fg="#27500A",
         meaning="Counted 8th from janma. Governs cooperation, goodwill, and "
                 "harmonious relationships.",
         significance="A mild but reliable auspicious tara, well suited to anything "
                       "involving other people.",
         dos=["Meetings and partnerships", "Social events", "Friendly negotiations",
              "Reconciliation"],
         avoids=["No major restriction"],
         tip="A good day to repair a relationship or start a collaboration."),
    dict(name="Parama Mitra", good=True, bg="#3B6D11", fg="#ffffff",
         meaning="Counted 9th from janma, the final tara in the cycle. Considered the "
                 "single most auspicious of the nine.",
         significance="Combines the strengths of all the favorable taras before it. "
                       "Ideal for the most significant undertakings.",
         dos=["Marriage and ceremonies", "Business launches", "Travel",
              "Signing important deals", "Griha pravesh"],
         avoids=["No major restriction"],
         tip="When you have a choice of dates for something major, this is usually "
             "the first tara to look for."),
]


def navtara_moon_info(y: int, mo: int, dd: int, hour_local: float, tz: float) -> dict:
    """Real (not average-projected) nakshatra/pada/navamsa for a given local date,
    evaluated at hour_local on that date."""
    ut_hours = hour_local - tz
    jd = julian_day(y, mo, dd, ut_hours)
    ayan = ayanamsa(jd)
    moon_sid = norm360(moon_longitude(jd) - ayan)
    nak_span = 360 / 27
    nak_idx = int(moon_sid // nak_span)
    frac = (moon_sid % nak_span) / nak_span
    pada = min(4, int(frac * 4) + 1)
    sign_idx = int(moon_sid // 30)
    return {
        "nak_idx": nak_idx, "frac": frac, "pada": pada, "sign_idx": sign_idx,
        "pada_sign_idx": navamsa_sign(moon_sid), "moon_sid": moon_sid,
    }


def navtara_tithi_info(y: int, mo: int, dd: int, hour_local: float, tz: float):
    ut_hours = hour_local - tz
    jd = julian_day(y, mo, dd, ut_hours)
    elong = norm360(moon_longitude(jd) - sun_longitude(jd))
    idx = int(elong // 12)
    paksha = "Shukla" if idx < 15 else "Krishna"
    local_idx = idx if idx < 15 else idx - 15
    if local_idx == 14:
        name = "Purnima" if paksha == "Shukla" else "Amavasya"
    else:
        name = TITHIS_ASCII[local_idx]
    return paksha, name


def navtara_tara_index(nak_idx: int, birth_nak_idx: int) -> int:
    return ((nak_idx - birth_nak_idx) % 27) % 9


# ============================================================
# COMPATIBILITY CHECK — Moon, Ascendant & Jupiter (focused synastry)
# ============================================================
# Deliberately NOT the full classical Ashtakoota Guna Milan (which checks
# eight factors — Varna, Vashya, Tara, Yoni, Graha Maitri, Gana, Bhakoot,
# Nadi — scored out of 36 and needs several more precise classical lookup
# tables than are built into this app). This is a focused subset checking
# only Moon, Ascendant, and Jupiter, as requested — scored out of its own
# 16-point scale so it's never confused with a genuine 36-point Guna Milan
# result. See the disclaimer shown alongside the results.

RASHI_LORD = {}
for _pk, _signs in OWN_SIGNS.items():
    for _s in _signs:
        RASHI_LORD[_s] = _pk


def _maitri_pair_score(k1: str, k2: str) -> float:
    """0-1 friendliness between two graha keys (their Naisargika Maitri, averaged
    both directions since the classical table isn't always symmetric)."""
    if k1 == k2:
        return 1.0
    rel1 = GRAHA_MAITRI.get(k1, {})
    rel2 = GRAHA_MAITRI.get(k2, {})
    def _side(rel, other):
        if other in rel.get("friends", []):
            return 1.0
        if other in rel.get("enemies", []):
            return 0.0
        return 0.5
    return (_side(rel1, k2) + _side(rel2, k1)) / 2


def compute_compatibility(chart_a: dict, chart_b: dict) -> dict:
    """Scores compatibility between two birth charts across Moon (nakshatra tara
    + rashi-lord friendship), Ascendant (lord friendship + house relationship),
    and Jupiter (dignity + cross-placement to the partner's Moon)."""
    a_moon = next(b for b in chart_a["bodies"] if b["key"] == "Mo")
    b_moon = next(b for b in chart_b["bodies"] if b["key"] == "Mo")
    a_asc = next(b for b in chart_a["bodies"] if b["key"] == "As")
    b_asc = next(b for b in chart_b["bodies"] if b["key"] == "As")
    a_jp = next(b for b in chart_a["bodies"] if b["key"] == "Jp")
    b_jp = next(b for b in chart_b["bodies"] if b["key"] == "Jp")

    components = []

    tara_ab = navtara_tara_index(b_moon["nakIdx"], a_moon["nakIdx"])
    tara_ba = navtara_tara_index(a_moon["nakIdx"], b_moon["nakIdx"])
    good_ab, good_ba = NAVTARA_INFO[tara_ab]["good"], NAVTARA_INFO[tara_ba]["good"]
    tara_score = (int(good_ab) + int(good_ba)) / 2 * 3
    components.append((
        "Moon Nakshatra Tara", tara_score, 3,
        f"{NAKSHATRAS[a_moon['nakIdx']]} \u2194 {NAKSHATRAS[b_moon['nakIdx']]} "
        f"({NAVTARA_INFO[tara_ab]['name']} / {NAVTARA_INFO[tara_ba]['name']})",
    ))

    a_moon_lord, b_moon_lord = RASHI_LORD[a_moon["sign"]], RASHI_LORD[b_moon["sign"]]
    moon_maitri_score = _maitri_pair_score(a_moon_lord, b_moon_lord) * 3
    components.append((
        "Moon Sign Lord Friendship", moon_maitri_score, 3,
        f"{SIGNS[a_moon['sign']]} ({a_moon_lord}) \u2194 {SIGNS[b_moon['sign']]} ({b_moon_lord})",
    ))

    a_asc_lord, b_asc_lord = RASHI_LORD[a_asc["sign"]], RASHI_LORD[b_asc["sign"]]
    lagna_maitri_score = _maitri_pair_score(a_asc_lord, b_asc_lord) * 2
    components.append((
        "Ascendant Lord Friendship", lagna_maitri_score, 2,
        f"{SIGNS[a_asc['sign']]} ({a_asc_lord}) \u2194 {SIGNS[b_asc['sign']]} ({b_asc_lord})",
    ))

    dist = ((b_asc["sign"] - a_asc["sign"]) % 12) + 1
    if dist in (1, 5, 9):
        house_score = 2.0
    elif dist in (4, 7, 10):
        house_score = 1.5
    elif dist in (6, 8, 12):
        house_score = 0.0
    else:
        house_score = 1.0
    components.append((
        "Ascendant House Relationship", house_score, 2, f"{dist} sign(s) apart",
    ))

    a_jp_dignity = graha_dignity("Jp", a_jp["sign"])
    b_jp_dignity = graha_dignity("Jp", b_jp["sign"])
    dignity_pts = {"Exalted": 1.5, "Own Sign": 1.5, "Neutral": 0.75, "Debilitated": 0.0}
    jp_dignity_score = dignity_pts[a_jp_dignity] + dignity_pts[b_jp_dignity]
    components.append((
        "Jupiter Dignity", jp_dignity_score, 3, f"{a_jp_dignity} / {b_jp_dignity}",
    ))

    dist_a_jp_to_b_moon = ((b_moon["sign"] - a_jp["sign"]) % 12) + 1
    dist_b_jp_to_a_moon = ((a_moon["sign"] - b_jp["sign"]) % 12) + 1
    good_counts = {1, 3, 5, 7, 9, 11}
    cross_score = (int(dist_a_jp_to_b_moon in good_counts) + int(dist_b_jp_to_a_moon in good_counts)) / 2 * 3
    components.append((
        "Jupiter \u2194 Moon Cross Placement", cross_score, 3,
        f"{dist_a_jp_to_b_moon} / {dist_b_jp_to_a_moon} sign(s) apart",
    ))

    total = sum(c[1] for c in components)
    max_total = sum(c[2] for c in components)
    pct = total / max_total * 100 if max_total else 0
    if pct >= 75:
        verdict = "Strong alignment"
    elif pct >= 55:
        verdict = "Good, workable alignment"
    elif pct >= 35:
        verdict = "Mixed — some friction likely"
    else:
        verdict = "Significant friction indicated"
    return {"components": components, "total": total, "max_total": max_total, "pct": pct, "verdict": verdict}


def render_navtara_chakra_tab(default_birth_nak_idx: int, tz: float):
    import calendar as _cal

    col_a, col_b = st.columns([1, 1])
    with col_a:
        birth_label = st.selectbox(
            "Janma Nakṣatra", NAKSHATRAS, index=default_birth_nak_idx, key="navtara_birth_nak"
        )
    birth_nak_idx = NAKSHATRAS.index(birth_label)

    today_ = date.today()
    month_opts = []
    for i in range(12):
        yy = today_.year + (today_.month - 1 + i) // 12
        mm_ = (today_.month - 1 + i) % 12 + 1
        month_opts.append((yy, mm_, datetime(yy, mm_, 1).strftime("%B %Y")))
    labels = [m[2] for m in month_opts]
    with col_b:
        sel_label = st.selectbox("Month", labels, index=0, key="navtara_month")
    year, month = next((yy, mm_) for yy, mm_, lbl in month_opts if lbl == sel_label)
    days_in_month = _cal.monthrange(year, month)[1]

    cell_html = ['<div style="display:grid;grid-template-columns:repeat(9,1fr);gap:6px;">']
    for day in range(1, days_in_month + 1):
        info = navtara_moon_info(year, month, day, 6.0, tz)
        t = NAVTARA_INFO[navtara_tara_index(info["nak_idx"], birth_nak_idx)]
        cell_html.append(
            f'<div style="background:{t["bg"]};color:{t["fg"]};border-radius:8px;'
            f'padding:8px 4px;text-align:center;">'
            f'<p style="font-size:15px;font-weight:700;margin:0;">{day}</p>'
            f'<p style="font-size:11px;margin:3px 0 0;line-height:1.25;">{NAKSHATRAS_ASCII[info["nak_idx"]]}</p>'
            f'<p style="font-size:10px;margin:2px 0 0;line-height:1.2;">{t["name"]}</p></div>'
        )
    cell_html.append("</div>")
    st.markdown("".join(cell_html), unsafe_allow_html=True)

    st.markdown(
        '<div style="display:flex;gap:14px;margin-top:14px;font-size:12px;flex-wrap:wrap;">'
        '<span><span style="display:inline-block;width:10px;height:10px;background:#173404;'
        'border-radius:2px;margin-right:5px;"></span>strongly auspicious</span>'
        '<span><span style="display:inline-block;width:10px;height:10px;background:#C0DD97;'
        'border-radius:2px;margin-right:5px;"></span>mildly auspicious</span>'
        '<span><span style="display:inline-block;width:10px;height:10px;background:#F7C1C1;'
        'border-radius:2px;margin-right:5px;"></span>mildly inauspicious</span>'
        '<span><span style="display:inline-block;width:10px;height:10px;background:#791F1F;'
        'border-radius:2px;margin-right:5px;"></span>strongly inauspicious</span>'
        '</div>', unsafe_allow_html=True,
    )

    default_day = today_.day if (today_.year == year and today_.month == month) else 1
    sel_day = st.number_input(
        "View details for day", min_value=1, max_value=days_in_month,
        value=default_day, step=1, key="navtara_day",
    )

    info = navtara_moon_info(year, month, int(sel_day), 6.0, tz)
    t = NAVTARA_INFO[navtara_tara_index(info["nak_idx"], birth_nak_idx)]
    paksha, tithi_name = navtara_tithi_info(year, month, int(sel_day), 6.0, tz)
    dos_html = "".join(f"<p style='margin:0 0 5px;font-size:14px;'>{x}</p>" for x in t["dos"])
    avoid_html = "".join(f"<p style='margin:0 0 5px;font-size:14px;'>{x}</p>" for x in t["avoids"])

    st.markdown(
        f"""
        <div class="kcard" style="margin-top:16px;">
          <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;">
            <p style="font-weight:700;font-size:17px;margin:0;">
              {datetime(year, month, int(sel_day)).strftime('%B %d, %Y')} — {NAKSHATRAS_ASCII[info['nak_idx']]}</p>
            <span style="background:{t['bg']};color:{t['fg']};padding:5px 14px;border-radius:6px;
              font-size:13px;">{t['name']} tara</span>
          </div>
          <p style="font-size:15px;color:{C['muted']};margin:10px 0 6px;">{t['meaning']}</p>
          <p style="font-size:14px;color:{C['muted']};margin:0 0 16px;">{t['significance']}</p>
          <div style="display:grid;grid-template-columns:1fr 1fr;gap:18px;margin-bottom:16px;">
            <div><h4 style="font-size:13px;color:#2f6f1f;margin:0 0 6px;">Favorable for</h4>{dos_html}</div>
            <div><h4 style="font-size:13px;color:#a3312f;margin:0 0 6px;">Avoid</h4>{avoid_html}</div>
          </div>
          <p style="font-size:12px;font-weight:700;color:{C['muted']};margin:0 0 3px;
            border-top:1px solid {C['line']};padding-top:10px;">NOTE</p>
          <p style="font-size:14px;margin:0 0 16px;">{t['tip']}</p>
          <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;
            border-top:1px solid {C['line']};padding-top:14px;">
            <div style="background:{C['panelSoft']};border-radius:8px;padding:10px 12px;">
              <p style="font-size:12px;color:{C['muted']};margin:0 0 2px;">Paksha</p>
              <p style="font-size:14px;font-weight:600;margin:0;">{paksha} Paksha</p></div>
            <div style="background:{C['panelSoft']};border-radius:8px;padding:10px 12px;">
              <p style="font-size:12px;color:{C['muted']};margin:0 0 2px;">Tithi</p>
              <p style="font-size:14px;font-weight:600;margin:0;">{tithi_name}</p></div>
            <div style="background:{C['panelSoft']};border-radius:8px;padding:10px 12px;">
              <p style="font-size:12px;color:{C['muted']};margin:0 0 2px;">Moon sign</p>
              <p style="font-size:14px;font-weight:600;margin:0;">{SIGNS_ASCII[info['sign_idx']]}</p></div>
            <div style="background:{C['panelSoft']};border-radius:8px;padding:10px 12px;">
              <p style="font-size:12px;color:{C['muted']};margin:0 0 2px;">Navamsa pada</p>
              <p style="font-size:14px;font-weight:600;margin:0;">Pada {info['pada']} — {SIGNS_ASCII[info['pada_sign_idx']]}</p></div>
          </div>
        </div>
        """,
        unsafe_allow_html=True,
    )
    st.caption(
        "Computed from this app's own Sun/Moon ephemeris for the exact date shown, rather than "
        "the average-lunar-period projection the original standalone tool used — no anchor date "
        "or re-projection drift."
    )


# ---- House classification relative to the lagna (1-indexed house numbers) ----
KENDRA_HOUSES = {1, 4, 7, 10}       # angular — strongest houses
TRIKONA_HOUSES = {1, 5, 9}          # trine — most auspicious (Dharma trikona)
UPACHAYA_HOUSES = {3, 6, 10, 11}    # growth houses — improve with time
DUSTHANA_HOUSES = {6, 8, 12}        # difficult houses

# ---- Puruṣārtha Trikoṇa: the four goals-of-life groupings, each a set of 3
# houses spaced 4 apart, each classically tied to one element (tattva).
HOUSE_TRIKONA_GROUP = {
    1: "Dharma Trikona (Fire)", 5: "Dharma Trikona (Fire)", 9: "Dharma Trikona (Fire)",
    2: "Artha Trikona (Earth)", 6: "Artha Trikona (Earth)", 10: "Artha Trikona (Earth)",
    3: "Kama Trikona (Air)", 7: "Kama Trikona (Air)", 11: "Kama Trikona (Air)",
    4: "Moksha Trikona (Water)", 8: "Moksha Trikona (Water)", 12: "Moksha Trikona (Water)",
}


def _house_tags(house_num: int) -> list:
    tags = []
    if house_num in KENDRA_HOUSES:
        tags.append("Kendra")
    if house_num in TRIKONA_HOUSES:
        tags.append("Trikona")
    if house_num in UPACHAYA_HOUSES:
        tags.append("Upachaya")
    if house_num in DUSTHANA_HOUSES:
        tags.append("Dusthana")
    return tags


TRIKONA_GROUP_HOUSES = {
    "Dharma Trikona (Fire)": (1, 5, 9),
    "Artha Trikona (Earth)": (2, 6, 10),
    "Kama Trikona (Air)": (3, 7, 11),
    "Moksha Trikona (Water)": (4, 8, 12),
}


def planets_by_trikona_group(bodies: list, asc_sign: int) -> dict:
    """Groups grahas (excludes the Ascendant point itself) by which Trikona
    element their occupied house belongs to, each list sorted ascending by
    degree-in-sign."""
    result = {name: [] for name in TRIKONA_GROUP_HOUSES}
    for b in bodies:
        if b["key"] == "As":
            continue
        house_num = ((b["sign"] - asc_sign) % 12) + 1
        for group_name, houses in TRIKONA_GROUP_HOUSES.items():
            if house_num in houses:
                result[group_name].append(b)
                break
    for entries in result.values():
        entries.sort(key=lambda b: b["inSign"])
    return result


def merge_trikona_entries(birth_entries: list, transit_entries: list) -> list:
    """Interleaves a group's birth and transit grahas into one list, sorted
    ascending by degree, each item tagged so the caller can colour transit
    entries differently instead of listing them in a separate block below."""
    merged = [dict(b, is_transit=False) for b in birth_entries]
    merged += [dict(b, is_transit=True) for b in transit_entries]
    merged.sort(key=lambda b: b["inSign"])
    return merged


def bodies_in_trikona_group(bodies: list, asc_sign: int, group_name: str) -> list:
    """Same house-membership test as planets_by_trikona_group, but for a single
    named group only — used to build the per-element mini-charts."""
    houses = TRIKONA_GROUP_HOUSES[group_name]
    out = []
    for b in bodies:
        if b["key"] == "As":
            continue
        house_num = ((b["sign"] - asc_sign) % 12) + 1
        if house_num in houses:
            out.append(b)
    return out


# ---- Simple Muhurta helpers: sunrise/sunset -> Rahu Kalam, Yamaganda, Gulika
# Kalam (inauspicious periods to avoid for new beginnings) and Abhijit Muhurta
# (the auspicious window straddling local solar noon). These are the classical
# day-length-divided-into-eighths / fifteenths rules used by most Panchang
# tools — general daily guidance, not activity-specific electional astrology
# (a proper muhurta for something like a wedding also weighs tithi, nakshatra,
# lagna, and various doshas well beyond what's computed here).
RAHU_KALAM_PART = [8, 2, 7, 5, 6, 4, 3]      # index 0=Sunday .. 6=Saturday
YAMAGANDA_PART = [5, 4, 3, 2, 1, 7, 6]
GULIKA_KALAM_PART = [7, 6, 5, 4, 3, 2, 1]


def sun_times_utc_hours(y: int, mo: int, dd: int, lat: float, lon: float):
    """Returns (sunrise, sunset, solar_noon) in UT decimal hours. Same low-precision
    approach as sunrise_utc_hours (no equation-of-time correction)."""
    jd_noon = julian_day(y, mo, dd, 12.0)
    sun_trop = sun_longitude(jd_noon)
    decl = declination(sun_trop, 0.0, jd_noon)
    lat_r, decl_r = lat * D2R, decl * D2R
    cosH = -math.tan(lat_r) * math.tan(decl_r)
    cosH = max(-1.0, min(1.0, cosH))
    H = math.acos(cosH) / D2R
    solar_noon = 12.0 - lon / 15.0
    return solar_noon - H / 15.0, solar_noon + H / 15.0, solar_noon


def _fmt_hm(hours_float: float) -> str:
    hours_float = hours_float % 24
    h = int(hours_float)
    m = int(round((hours_float - h) * 60))
    if m == 60:
        m = 0
        h = (h + 1) % 24
    return f"{h:02d}:{m:02d}"


def compute_muhurta_windows(y: int, mo: int, dd: int, lat: float, lon: float, tz: float) -> dict:
    sunrise_ut, sunset_ut, noon_ut = sun_times_utc_hours(y, mo, dd, lat, lon)
    sunrise_local = sunrise_ut + tz
    sunset_local = sunset_ut + tz
    noon_local = noon_ut + tz
    day_len = sunset_local - sunrise_local
    weekday = date(y, mo, dd).isoweekday() % 7  # 0=Sunday .. 6=Saturday

    def part_window(part_idx):
        start = sunrise_local + (part_idx - 1) * day_len / 8
        return start, start + day_len / 8

    muhurta_len = day_len / 15
    return {
        "sunrise": sunrise_local,
        "sunset": sunset_local,
        "rahu_kalam": part_window(RAHU_KALAM_PART[weekday]),
        "yamaganda": part_window(YAMAGANDA_PART[weekday]),
        "gulika_kalam": part_window(GULIKA_KALAM_PART[weekday]),
        "abhijit": (noon_local - muhurta_len / 2, noon_local + muhurta_len / 2),
    }


# ============================================================
# HORA — 24 planetary hours (12 day + 12 night), Chaldean sequence
# ============================================================
# Classical technique: sunrise-to-sunset is split into 12 equal "day horas",
# and that sunset to the NEXT sunrise into 12 equal "night horas", each ruled
# by one of the 7 classical grahas cycling continuously in Chaldean order
# (Saturn, Jupiter, Mars, Sun, Venus, Mercury, Moon, repeat). The first hora
# of any day is ruled by that weekday's own lord.

HORA_LORDS_CHALDEAN = ["Sa", "Jp", "Ma", "Su", "Ve", "Me", "Mo"]
# weekday index (0=Sun..6=Sat) -> that day's lord's position in the Chaldean list above
WEEKDAY_HORA_START_IDX = {0: 3, 1: 6, 2: 2, 3: 5, 4: 1, 5: 4, 6: 0}

HORA_EFFECTIVENESS = {
    "Su": "Most-effective", "Ma": "Most-effective", "Jp": "Most-effective",
    "Sa": "Detrimental", "Me": "Less-effective", "Ve": "Neutral", "Mo": "Neutral",
}


def compute_hora_table(y: int, mo: int, dd: int, lat: float, lon: float, tz: float) -> dict:
    """Returns {'day': [...12 horas...], 'night': [...12 horas...]}, each hora
    a dict with lord, start, end (local decimal hours), effectiveness, and
    whether its end time rolls into the next calendar day."""
    sunrise_ut, sunset_ut, _ = sun_times_utc_hours(y, mo, dd, lat, lon)
    next_d = date(y, mo, dd) + timedelta(days=1)
    next_sunrise_ut, _, _ = sun_times_utc_hours(next_d.year, next_d.month, next_d.day, lat, lon)

    sunrise_local = sunrise_ut + tz
    sunset_local = sunset_ut + tz
    next_sunrise_local = next_sunrise_ut + tz + 24  # relative to this day's start, for continuous math

    weekday = date(y, mo, dd).isoweekday() % 7
    start_idx = WEEKDAY_HORA_START_IDX[weekday]

    day_len = sunset_local - sunrise_local
    night_len = next_sunrise_local - sunset_local
    day_step = day_len / 12
    night_step = night_len / 12

    def build(n_horas, base_start, step, idx_offset):
        horas = []
        for i in range(n_horas):
            lord = HORA_LORDS_CHALDEAN[(start_idx + idx_offset + i) % 7]
            h_start = base_start + i * step
            h_end = h_start + step
            horas.append({
                "lord": lord,
                "start": h_start % 24,
                "end": h_end % 24,
                "effectiveness": HORA_EFFECTIVENESS[lord],
                "next_day": h_end >= 24,
            })
        return horas

    day_horas = build(12, sunrise_local, day_step, 0)
    night_horas = build(12, sunset_local, night_step, 12)
    return {"day": day_horas, "night": night_horas}


# ============================================================
# MUHURTA FINDER — activity-based electional search
# ============================================================
# General traditional guidance compiled from commonly published Panchang
# references (favourable weekday + nakshatra per activity type). This is
# NOT a substitute for a full professional muhurta consultation, which also
# weighs the specific lagna at the moment, planetary strength/affliction,
# and doshas beyond what's checked here — see the caveat shown with results.

MUHURTA_ACTIVITIES = {
    "Buy a vehicle": {
        "weekdays": [3, 4, 5],  # Wed, Thu, Fri
        "nakshatras": [0, 4, 6, 7, 12, 13, 14, 16, 21, 22, 26],  # Aswini, Mrigashira, Punarvasu, Pushya, Hasta, Chitra, Swati, Anuradha, Shravana, Dhanishtha, Revati
    },
    "Buy or register property": {
        "weekdays": [1, 3, 4, 5],  # Mon, Wed, Thu, Fri
        "nakshatras": [3, 4, 11, 12, 14, 16, 20, 25, 26],  # Rohini, Mrigashira, U.Phalguni, Hasta, Swati, Anuradha, U.Ashadha, U.Bhadrapada, Revati
    },
    "Griha Pravesh": {
        "weekdays": [1, 3, 4, 5],  # Mon, Wed, Thu, Fri
        "nakshatras": [3, 4, 11, 12, 14, 16, 20, 25, 26],
    },
    "Start a business": {
        "weekdays": [3, 4, 5],  # Wed, Thu, Fri
        "nakshatras": [0, 7, 12, 13, 14, 16, 26],  # Aswini, Pushya, Hasta, Chitra, Swati, Anuradha, Revati
    },
    "Starting a New Job": {
        "weekdays": [1, 3, 4, 5],  # Mon, Wed, Thu, Fri
        "nakshatras": [0, 7, 11, 12, 13, 14, 16, 20, 25, 26],  # Aswini, Pushya, U.Phalguni, Hasta, Chitra, Swati, Anuradha, U.Ashadha, U.Bhadrapada, Revati
    },
    "Sign an agreement": {
        "weekdays": [3, 4, 5],
        "nakshatras": [0, 7, 12, 13, 14, 16, 26],
    },
    "Begin travel": {
        "weekdays": [0, 1, 3, 4, 5],  # Sun, Mon, Wed, Thu, Fri
        "nakshatras": [0, 7, 12, 21, 26],  # Aswini, Pushya, Hasta, Shravana, Revati
    },
    "Spiritual practice": {
        "weekdays": [1, 4, 5],  # Mon, Thu, Fri
        "nakshatras": [7, 11, 20, 21, 25, 26],  # Pushya, U.Phalguni, U.Ashadha, Shravana, U.Bhadrapada, Revati
        "relax_tithi_rule": True,  # rikta/amavasya avoidance doesn't apply the same way here
    },
}

RIKTA_TITHI_IDX = {3, 8, 13}  # 4th, 9th, 14th of each paksha (0-indexed within paksha)


def find_muhurta_windows(activity: str, start_date: date, range_days: int, lat: float, lon: float, tz: float,
                          exclude_kalam_overlap: bool = True, max_results: int = 10):
    """Scans a date range and scores each day's Abhijit Muhurta window against
    classical rules for the given activity: favourable weekday, favourable
    nakshatra (Moon's nakshatra at midday), and avoiding rikta/amavasya tithi.
    Returns the top-scoring days (score = fraction of rules satisfied)."""
    rules = MUHURTA_ACTIVITIES.get(activity)
    if rules is None:
        return []
    results = []
    for i in range(range_days):
        d = start_date + timedelta(days=i)
        mw = compute_muhurta_windows(d.year, d.month, d.day, lat, lon, tz)
        abhijit_mid_hour = (mw["abhijit"][0] + mw["abhijit"][1]) / 2
        hh = int(abhijit_mid_hour) % 24
        mm = int(round((abhijit_mid_hour % 1) * 60))
        chart = compute_chart(d.year, d.month, d.day, hh, mm, lat, lon, tz)
        pan = chart["panchanga"]
        weekday = d.isoweekday() % 7

        checks = []
        checks.append(weekday in rules["weekdays"])
        if not rules.get("relax_tithi_rule"):
            tithi_in_paksha = pan["tithiIdx"] % 15
            checks.append(tithi_in_paksha not in RIKTA_TITHI_IDX and pan["tithiIdx"] != 29)
        checks.append(pan["nakIdx"] in rules["nakshatras"])
        if exclude_kalam_overlap:
            a0, a1 = mw["abhijit"]
            overlaps = False
            for k in ("rahu_kalam", "yamaganda", "gulika_kalam"):
                k0, k1 = mw[k]
                if a0 < k1 and k0 < a1:
                    overlaps = True
            checks.append(not overlaps)

        score = sum(checks) / len(checks) if checks else 0
        if score >= 0.5:
            results.append({
                "date": d, "weekday": weekday, "score": score,
                "abhijit": mw["abhijit"], "tithi_idx": pan["tithiIdx"],
                "paksha": pan["paksha"], "tithi_name": pan["tithiName"],
                "yoga_idx": pan["yogaIdx"], "nak_idx": pan["nakIdx"],
            })
    results.sort(key=lambda r: (-r["score"], r["date"]))
    return results[:max_results]


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
            nak_abbr = NAK_ABBR_ASCII[b["nakIdx"]]
            lines.append(f'{_ascii_key(b["key"])} {deg}\u00b0{retro} {nak_abbr}')

        block_h = len(lines) * 4.2
        pdf.set_font("Helvetica", "", 7)
        pdf.set_text_color(122, 111, 92)
        pdf.text(cx - 3, cy - block_h / 2 - 3, str(sign_num))

        ty = cy - block_h / 2
        for line in lines:
            pdf.set_font("Helvetica", "B", 7)
            pdf.set_text_color(196, 70, 43) if (line.startswith("As ")) else pdf.set_text_color(58, 46, 31)
            pdf.set_xy(cx - 20, ty)
            pdf.cell(40, 4.2, line, align="C")
            ty += 4.2


def _hex_rgb(h: str):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


PLANET_TRANSIT_COLORS_RGB = {k: _hex_rgb(v) for k, v in PLANET_TRANSIT_COLORS.items()}


def draw_combined_diamond_chart_pdf(pdf, birth_bodies, transit_bodies, asc_sign: int,
                                     asc_body: dict, x0: float, y0: float, size: float):
    """Single diamond chart with birth AND transit grahas merged, ascending by
    degree per house. Birth stays black; each transit graha gets its own fixed
    colour (PLANET_TRANSIT_COLORS_RGB)."""
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
    for b in birth_bodies:
        if b["key"] == "As":
            continue
        by_house[(b["sign"] - asc_sign + 12) % 12].append(dict(b, _is_transit=False))
    for b in transit_bodies:
        if b["key"] == "As":
            continue
        by_house[(b["sign"] - asc_sign + 12) % 12].append(dict(b, _is_transit=True))
    for entries in by_house:
        entries.sort(key=lambda b: b["inSign"])

    for h, (fx, fy) in enumerate(HOUSE_FRACS):
        cx, cy = x0 + fx * size, y0 + fy * size
        sign_num = ((asc_sign + h) % 12) + 1
        lines = []
        if h == 0:
            lines.append(("As " + str(int(asc_body["inSign"])) + "\u00b0", (58, 46, 31)))
        for b in by_house[h]:
            deg = int(b["inSign"])
            retro = "R" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
            color = PLANET_TRANSIT_COLORS_RGB.get(b["key"], (196, 70, 43)) if b["_is_transit"] else (58, 46, 31)
            lines.append((f'{_ascii_key(b["key"])} {deg}\u00b0{retro}', color))

        block_h = len(lines) * 4.2
        pdf.set_font("Helvetica", "", 7)
        pdf.set_text_color(122, 111, 92)
        pdf.text(cx - 3, cy - block_h / 2 - 3, str(sign_num))

        ty = cy - block_h / 2
        for line_text, color in lines:
            pdf.set_font("Helvetica", "B", 7)
            pdf.set_text_color(*color)
            pdf.set_xy(cx - 20, ty)
            pdf.cell(40, 4.2, line_text, align="C")
            ty += 4.2


def generate_kundali_pdf_bytes(birth_chart, form, transit_chart=None) -> bytes:
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

    # ---------------- Page 5: Nakshatra Details, Graha Maitri, Houses, Muhurta ----------------
    pdf.add_page()
    banner("ASTROLOGICAL INSIGHTS", "Nakshatra Details, Graha Maitri, Houses & Muhurta")

    section("Nakshatra Details (each graha's birth nakshatra)")
    nak_detail_rows = []
    for b in core_bodies:
        idx = b["nakIdx"]
        nak_detail_rows.append((
            BODY_FULLNAME_ASCII.get(b["key"], b["key"]),
            NAKSHATRAS_ASCII[idx],
            NAKSHATRA_DEITY_ASCII[idx],
            NAKSHATRA_SYMBOL_ASCII[idx],
        ))
    table(["Graha", "Nakshatra", "Deity", "Symbol"], nak_detail_rows, [34, 42, 46, 48], row_h=6.5)

    pdf.ln(3)
    pdf.set_font("Helvetica", "B", 10)
    pdf.set_text_color(*GOLD)
    pdf.cell(0, 6, "Why it helps or challenges (Nakshatra Lord Relationship)", ln=True)
    pdf.set_font("Helvetica", "", 8.5)
    for b in core_bodies:
        note = nakshatra_lord_relationship_note(b["key"], b["nakIdx"])
        pdf.set_text_color(*IVORY)
        pdf.set_font("Helvetica", "B", 8.5)
        pdf.cell(30, 5, BODY_FULLNAME_ASCII.get(b["key"], b["key"]), border=0)
        pdf.set_font("Helvetica", "", 8.5)
        pdf.set_text_color(*MUTED)
        pdf.multi_cell(0, 5, note)
    pdf.ln(1)

    section("Graha Maitri (Classical Planetary Friendship)")
    maitri_rows = []
    for k in ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa"]:
        rel = GRAHA_MAITRI[k]
        fmt_list = lambda ks: ", ".join(BODY_FULLNAME_ASCII.get(x, x).split(" ")[0] for x in ks) if ks else "-"
        maitri_rows.append((
            BODY_FULLNAME_ASCII[k], fmt_list(rel["friends"]), fmt_list(rel["neutral"]), fmt_list(rel["enemies"]),
        ))
    table(["Graha", "Friends", "Neutral", "Enemies"], maitri_rows, [36, 52, 52, 30], row_h=6.5)
    pdf.set_font("Helvetica", "I", 7.5)
    pdf.set_text_color(*MUTED)
    pdf.multi_cell(0, 4,
        "Naisargika (natural, fixed) friendship per Brihat Parashara Hora Shastra - not "
        "adjusted for house placement in this chart (Tatkalika/compound friendship). "
        "Rahu and Ketu are shadow points and fall outside this classical scheme.")

    section("House Classification (relative to the Lagna)")
    house_rows = []
    for h in range(1, 13):
        tags = _house_tags(h)
        house_rows.append((
            str(h), SIGNS_ASCII[(b_asc["sign"] + h - 1) % 12],
            ", ".join(tags) if tags else "-", HOUSE_TRIKONA_GROUP[h],
        ))
    table(["House", "Sign", "Classification", "Trikona Group"], house_rows, [16, 44, 60, 60], row_h=6)
    pdf.set_font("Helvetica", "I", 7.5)
    pdf.set_text_color(*MUTED)
    pdf.multi_cell(0, 4,
        "Kendra (1,4,7,10) = angular, strongest houses. Trikona (1,5,9) = trine, most "
        "auspicious. Upachaya (3,6,10,11) = grow stronger over time. Dusthana (6,8,12) = "
        "difficult houses. Trikona Group = the four goals-of-life groupings (Dharma/Artha/"
        "Kama/Moksha), each tied to one element: 1,5,9 = Fire; 2,6,10 = Earth; "
        "3,7,11 = Air; 4,8,12 = Water.")

    section("Grahas by Trikona Group (ascending by degree)")
    trikona_planets = planets_by_trikona_group(core_bodies, b_asc["sign"])
    transit_core_bodies = (
        [b for b in transit_chart["bodies"] if b["key"] in CORE_KEYS] if transit_chart else []
    )
    trikona_transit = (
        planets_by_trikona_group(transit_core_bodies, b_asc["sign"]) if transit_core_bodies else {}
    )
    for group_name in trikona_planets:
        entries = trikona_planets[group_name]
        t_entries = trikona_transit.get(group_name, [])
        merged = merge_trikona_entries(entries, t_entries)
        pdf.set_font("Helvetica", "B", 10)
        pdf.set_text_color(*GOLD)
        pdf.cell(0, 6.5, group_name, ln=True)
        pdf.set_font("Helvetica", "", 9.5)
        if merged:
            for i, b in enumerate(merged):
                pdf.set_text_color(*(PLANET_TRANSIT_COLORS_RGB.get(b["key"], SINDOOR) if b["is_transit"] else IVORY))
                text = f'{_ascii_key(b["key"])} {int(b["inSign"])}\u00b0 ({SIGNS_ASCII[b["sign"]]})'
                if i < len(merged) - 1:
                    text += ", "
                pdf.write(5, text)
            pdf.ln(7)
        else:
            pdf.set_text_color(*MUTED)
            pdf.multi_cell(0, 5, "No grahas placed in this group's houses.")
        pdf.ln(2)
    pdf.set_font("Helvetica", "I", 7.5)
    pdf.set_text_color(*IVORY)
    pdf.write(4, "Black")
    pdf.set_text_color(*MUTED)
    pdf.write(4, " = birth position   ")
    pdf.set_text_color(*SINDOOR)
    pdf.write(4, "Red")
    pdf.set_text_color(*MUTED)
    pdf.write(4, " = current transit position")
    pdf.ln(8)

    section("Muhurta - Auspicious & Inauspicious Timings (birth date)")
    lat_, lon_, tz_ = form["city"][2], form["city"][3], form["city"][4]
    mw = compute_muhurta_windows(form["dob"].year, form["dob"].month, form["dob"].day, lat_, lon_, tz_)
    muhurta_rows = [
        ("Sunrise", _fmt_hm(mw["sunrise"]), "-"),
        ("Sunset", _fmt_hm(mw["sunset"]), "-"),
        ("Abhijit Muhurta", f'{_fmt_hm(mw["abhijit"][0])} - {_fmt_hm(mw["abhijit"][1])}', "Auspicious"),
        ("Rahu Kalam", f'{_fmt_hm(mw["rahu_kalam"][0])} - {_fmt_hm(mw["rahu_kalam"][1])}', "Avoid"),
        ("Yamaganda", f'{_fmt_hm(mw["yamaganda"][0])} - {_fmt_hm(mw["yamaganda"][1])}', "Avoid"),
        ("Gulika Kalam", f'{_fmt_hm(mw["gulika_kalam"][0])} - {_fmt_hm(mw["gulika_kalam"][1])}', "Avoid"),
    ]
    table(["Period", "Window (local time)", "Guidance"], muhurta_rows, [50, 70, 50], row_h=7)
    pdf.set_font("Helvetica", "I", 7.5)
    pdf.set_text_color(*MUTED)
    pdf.multi_cell(0, 4,
        "General daily guidance only (day divided into 8/15 parts between sunrise and "
        "sunset; no equation-of-time correction) - not a substitute for a full electional "
        "(muhurta) analysis for a specific event, which also weighs tithi, nakshatra, "
        "lagna, and relevant doshas.")

    # ---------------- Page 6: Combined Trikona Chart (birth + transit, one chart) ----------------
    pdf.add_page()
    banner("TRIKONA CHART", "Birth & Current Transit Together - Fire, Earth, Air, Water")
    chart_size = 130
    x0 = (210 - chart_size) / 2
    y0 = 42
    draw_combined_diamond_chart_pdf(pdf, core_bodies, transit_core_bodies, b_asc["sign"], b_asc, x0, y0, chart_size)
    pdf.set_y(y0 + chart_size + 8)
    legend_items = [
        ("Birth (black)", (58, 46, 31)),
        ("Su", PLANET_TRANSIT_COLORS_RGB["Su"]), ("Mo", PLANET_TRANSIT_COLORS_RGB["Mo"]),
        ("Ma", PLANET_TRANSIT_COLORS_RGB["Ma"]), ("Me", PLANET_TRANSIT_COLORS_RGB["Me"]),
        ("Jp", PLANET_TRANSIT_COLORS_RGB["Jp"]), ("Ve", PLANET_TRANSIT_COLORS_RGB["Ve"]),
        ("Sa", PLANET_TRANSIT_COLORS_RGB["Sa"]), ("Ra/Ke", PLANET_TRANSIT_COLORS_RGB["Ra"]),
    ]
    pdf.set_font("Helvetica", "B", 8)
    pdf.set_x(15)
    for i, (label_, color) in enumerate(legend_items):
        pdf.set_text_color(*color)
        pdf.write(5, label_)
        if i < len(legend_items) - 1:
            pdf.set_text_color(*MUTED)
            pdf.write(5, "   -   ")
    pdf.ln(8)
    pdf.set_font("Helvetica", "I", 8)
    pdf.set_text_color(*MUTED)
    pdf.multi_cell(0, 4.5,
        "All grahas, birth and current transit together, listed ascending by degree within "
        "each house. Birth positions are always black; each transit graha keeps its own fixed "
        "colour so it's identifiable at a glance regardless of which house it's currently in.")

    out = pdf.output(dest="S")
    return out.encode("latin-1") if isinstance(out, str) else bytes(out)


def generate_kundali_html_report(birth_chart, form, transit_chart=None) -> str:
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

    nak_detail_rows = "".join(
        f"<tr><td>{b['key']}</td><td>{NAKSHATRAS[b['nakIdx']]}</td>"
        f"<td>{NAKSHATRA_DEITY_ASCII[b['nakIdx']]}</td><td>{NAKSHATRA_SYMBOL_ASCII[b['nakIdx']]}</td>"
        f"<td style='font-size:13px;'>{nakshatra_lord_relationship_note(b['key'], b['nakIdx'])}</td></tr>"
        for b in core_bodies
    )

    def _maitri_list(ks):
        return ", ".join(BODY_FULLNAME_ASCII.get(k, k) for k in ks) if ks else "—"

    maitri_rows = "".join(
        f"<tr><td>{BODY_FULLNAME_ASCII[k]}</td><td>{_maitri_list(v['friends'])}</td>"
        f"<td>{_maitri_list(v['neutral'])}</td><td>{_maitri_list(v['enemies'])}</td></tr>"
        for k, v in GRAHA_MAITRI.items()
    )

    house_rows = "".join(
        f"<tr><td>{h}</td><td>{SIGNS[(b_asc['sign'] + h - 1) % 12]}</td>"
        f"<td>{', '.join(_house_tags(h)) or '—'}</td><td>{HOUSE_TRIKONA_GROUP[h]}</td></tr>"
        for h in range(1, 13)
    )

    _trikona_planets = planets_by_trikona_group(core_bodies, b_asc["sign"])
    _transit_core_bodies = (
        [b for b in transit_chart["bodies"] if b["key"] in CORE_KEYS] if transit_chart else []
    )
    _trikona_transit = (
        planets_by_trikona_group(_transit_core_bodies, b_asc["sign"]) if _transit_core_bodies else {}
    )

    def _trikona_merged_cell(birth_entries, transit_entries):
        merged = merge_trikona_entries(birth_entries, transit_entries)
        if not merged:
            return "—"
        parts = []
        for b in merged:
            color = PLANET_TRANSIT_COLORS.get(b["key"], "#C4462B") if b["is_transit"] else "#3A2E1F"
            parts.append(f'<span style="color:{color};">{b["key"]} {int(b["inSign"])}\u00b0 ({SIGNS[b["sign"]]})</span>')
        return ", ".join(parts)

    trikona_group_rows = "".join(
        f"<tr><td class='k' style='width:30%;'>{group_name}</td>"
        f"<td>{_trikona_merged_cell(entries, _trikona_transit.get(group_name, []))}</td></tr>"
        for group_name, entries in _trikona_planets.items()
    )

    # ---- One combined diamond chart: birth + transit grahas merged, ascending
    # by degree per house, each transit graha in its own fixed colour ----
    combined_chart_svg = build_combined_diamond_svg(core_bodies, _transit_core_bodies, b_asc["sign"])
    trikona_legend_html = (
        f'<span style="color:#3A2E1F;font-weight:700;">Birth (black)</span>'
        + "".join(
            f' &middot; <span style="color:{PLANET_TRANSIT_COLORS[k]};font-weight:700;">{k}</span>'
            for k in ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa"]
        )
        + f' &middot; <span style="color:{PLANET_TRANSIT_COLORS["Ra"]};font-weight:700;">Ra/Ke</span>'
    )

    _lat, _lon, _tz = form["city"][2], form["city"][3], form["city"][4]
    _mw = compute_muhurta_windows(form["dob"].year, form["dob"].month, form["dob"].day, _lat, _lon, _tz)
    muhurta_rows = "".join([
        f"<tr><td>Sunrise</td><td>{_fmt_hm(_mw['sunrise'])}</td><td>—</td></tr>",
        f"<tr><td>Sunset</td><td>{_fmt_hm(_mw['sunset'])}</td><td>—</td></tr>",
        f"<tr class='active'><td>Abhijit Muhūrta</td><td>{_fmt_hm(_mw['abhijit'][0])} – {_fmt_hm(_mw['abhijit'][1])}</td><td>Auspicious</td></tr>",
        f"<tr><td>Rāhu Kālam</td><td>{_fmt_hm(_mw['rahu_kalam'][0])} – {_fmt_hm(_mw['rahu_kalam'][1])}</td><td>Avoid</td></tr>",
        f"<tr><td>Yamaganda</td><td>{_fmt_hm(_mw['yamaganda'][0])} – {_fmt_hm(_mw['yamaganda'][1])}</td><td>Avoid</td></tr>",
        f"<tr><td>Gulika Kālam</td><td>{_fmt_hm(_mw['gulika_kalam'][0])} – {_fmt_hm(_mw['gulika_kalam'][1])}</td><td>Avoid</td></tr>",
    ])

    now_utc_ = datetime.utcnow()
    dasha_rows = "".join(
        f"<tr class=\"{'active' if d['from'] <= now_utc_ < d['to'] else ''}\">"
        f"<td>{d['lord']}</td><td>{d['from'].strftime('%d %b %Y')}</td>"
        f"<td>{d['to'].strftime('%d %b %Y')}</td><td>{d['yrs']:.1f} yrs</td></tr>"
        for d in birth_chart["dashas"]
    )

    # ---- Real diamond (North-Indian) chart, reusing the same accurate SVG
    # generator as the on-screen app — draws the outer square, both diagonals,
    # AND the inner diamond connecting each side's midpoint, which together are
    # what actually divide the chart into all 12 house boxes. (An earlier
    # version of this report faked it with pure CSS gradients and only drew
    # the two diagonals, leaving the chart looking like 4 boxes instead of 12.)
    chart_svg = build_svg_chart(core_bodies, [], b_asc["sign"], show_nakshatra=True)
    chart_html = f'<div style="display:flex;justify-content:center;margin:20px 0;">{chart_svg}</div>'

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

  <h2>Nakṣatra Details</h2>
  <table>
    <tr><th>Graha</th><th>Nakṣatra</th><th>Deity</th><th>Symbol</th><th>Significance</th></tr>
    {nak_detail_rows}
  </table>

  <h2>Graha Maitri · Planetary Friendship</h2>
  <table>
    <tr><th>Graha</th><th>Friends</th><th>Neutral</th><th>Enemies</th></tr>
    {maitri_rows}
  </table>
  <p class="footer" style="text-align:left;margin-top:10px;">Naisargika (natural, fixed) friendship per Bṛhat Parāśara
  Horā Śāstra — not adjusted for house placement in this chart. Rāhu/Ketu fall outside this classical scheme.</p>

  <h2>House Classification</h2>
  <table>
    <tr><th>House</th><th>Sign</th><th>Classification</th><th>Trikoṇa Group</th></tr>
    {house_rows}
  </table>
  <p class="footer" style="text-align:left;margin-top:10px;">Kendra (1,4,7,10) = angular. Trikoṇa (1,5,9) = trine,
  most auspicious. Upachaya (3,6,10,11) = grow stronger over time. Dusthāna (6,8,12) = difficult houses.
  Trikoṇa Group = the four goals-of-life groupings (Dharma/Artha/Kāma/Mokṣa), each tied to one element:
  1,5,9 = Fire; 2,6,10 = Earth; 3,7,11 = Air; 4,8,12 = Water.</p>

  <h2>Grahas by Trikoṇa Group (ascending by degree)</h2>
  <table>
    <tr><th>Trikoṇa Group</th><th>Grahas</th></tr>
    {trikona_group_rows}
  </table>
  <p class="footer" style="text-align:left;margin-top:6px;">{trikona_legend_html}</p>

  <h2>Trikoṇa Chart &middot; Birth &amp; Current Transit Together</h2>
  <div style="text-align:center;">{combined_chart_svg}</div>
  <p class="footer" style="text-align:left;margin-top:10px;">{trikona_legend_html}<br>
  All grahas, birth and current transit together, listed ascending by degree within each house.
  Birth positions are always black; each transit graha keeps its own fixed colour so it's
  identifiable at a glance regardless of which house it's currently in.</p>

  <h2>Muhūrta · Timings on the Birth Date</h2>
  <table>
    <tr><th>Period</th><th>Window (local time)</th><th>Guidance</th></tr>
    {muhurta_rows}
  </table>
  <p class="footer" style="text-align:left;margin-top:10px;">General daily guidance only (sunrise-to-sunset divided
  into 8/15 parts, no equation-of-time correction) — not a substitute for a full electional analysis for a specific
  event, which also weighs tithi, nakṣatra, lagna, and relevant doṣas.</p>

  <p class="footer">Generated by Kuṇḍalī · Lahiri ayanāṁśa engine · houses fixed to the birth lagna.<br>
  Engine accuracy: Sun/Moon within a few arc-minutes, other grahas ~0.1–0.5°, mean node.</p>
</body></html>
"""


# ============================================================
# RAZORPAY — real payments (+ automatic Test Mode when unconfigured)
# ============================================================
#
# Reads credentials from environment variables. On Render: your service ->
# Environment -> add RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET, APP_BASE_URL.
# Use the rzp_test_... keys first end-to-end before switching to rzp_live_....

RAZORPAY_KEY_ID = os.environ.get("RAZORPAY_KEY_ID", "")
RAZORPAY_KEY_SECRET = os.environ.get("RAZORPAY_KEY_SECRET", "")
APP_BASE_URL = os.environ.get("APP_BASE_URL", "").rstrip("/")
PREMIUM_PRICE_INR = 299
PREMIUM_PRICE_PAISE = PREMIUM_PRICE_INR * 100

RAZORPAY_CONFIGURED = bool(RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET and APP_BASE_URL)

# True when real Razorpay Test Mode keys (rzp_test_...) are configured, as opposed to
# live keys (rzp_live_...) or no keys at all. Test Mode still opens the REAL Razorpay
# checkout — it just needs Razorpay's own dummy/test payment credentials, not real ones.
RAZORPAY_TEST_KEY = RAZORPAY_KEY_ID.startswith("rzp_test_")

# ---- Test mode: lets you exercise the ENTIRE premium flow (order created,
# payment "completes", the same DB writes a real payment would trigger,
# premium flag flips, report unlocks) without any real money moving and
# without needing Razorpay keys at all. Controlled by one environment
# variable so it can never accidentally stay on in production:
#   - If RAZORPAY_KEY_ID/SECRET/APP_BASE_URL are NOT all set, test mode
#     turns on automatically (there's no way to charge a real card anyway).
#   - Once you add real Razorpay keys on Render, RAZORPAY_CONFIGURED becomes
#     True and test mode turns itself off automatically.
#   - PAYMENT_TEST_MODE=1 forces test mode on even with real keys present,
#     for staging. Never set this on a production deployment that takes
#     real customer payments.
PAYMENT_TEST_MODE = (
    os.environ.get("PAYMENT_TEST_MODE", "").strip().lower() in ("1", "true", "yes")
    or not RAZORPAY_CONFIGURED
)


def razorpay_create_payment_link(amount_paise: int, user_id: int, description: str, user_name: str = "") -> dict:
    """Creates a Razorpay Payment Link — a real, hosted Razorpay page with its own
    URL. The customer is sent there with a normal link (new tab), completes
    payment on Razorpay's own domain, and Razorpay redirects them back to
    callback_url when done. No iframe embedding anywhere in this flow, which
    sidesteps the sizing/clipping problems that Checkout.js-in-an-iframe had."""
    payload = {
        "amount": amount_paise,
        "currency": "INR",
        "description": description,
        "reference_id": f"user{user_id}-{int(time.time())}-{secrets.token_hex(3)}",
        "callback_url": f"{APP_BASE_URL}/",
        "callback_method": "get",
    }
    if user_name:
        payload["customer"] = {"name": user_name}
    resp = requests.post(
        "https://api.razorpay.com/v1/payment_links",
        auth=(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET),
        json=payload,
        timeout=15,
    )
    resp.raise_for_status()
    return resp.json()


def razorpay_verify_payment_link_signature(plink_id: str, reference_id: str, status: str,
                                            payment_id: str, signature: str) -> bool:
    """Razorpay's documented Payment Link signature check: HMAC-SHA256 of
    'payment_link_id|payment_link_reference_id|payment_link_status|razorpay_payment_id'
    using the account's key secret."""
    msg = f"{plink_id}|{reference_id}|{status}|{payment_id}".encode("utf-8")
    expected = hmac.new(RAZORPAY_KEY_SECRET.encode("utf-8"), msg, hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected, signature)


def simulate_test_payment(user_id: int, amount_paise: int) -> bool:
    """Test-mode stand-in for the real Razorpay round trip. Creates a synthetic
    order + payment id (clearly prefixed 'test_' so they can never collide with
    or be mistaken for real Razorpay ids), writes them through the exact same
    payments-ledger functions the real flow uses, then flips is_premium. No
    network call, no Razorpay checkout, no money movement of any kind."""
    order_id = f"test_order_{secrets.token_hex(10)}"
    payment_id = f"test_pay_{secrets.token_hex(10)}"
    record_order(user_id, order_id, amount_paise)
    ok = mark_order_paid(order_id, payment_id)
    if ok:
        set_premium(user_id, True)
    return ok


def handle_razorpay_return():
    """Runs on every rerun, before anything else, so a payment redirect is verified
    and applied exactly once even if the page is refreshed afterwards. Deliberately
    does NOT depend on st.session_state['user'] being present — a full-page
    redirect back from Razorpay can land in a fresh browser session, so the
    account to credit comes from the payments ledger (order_owner), not from
    whoever happens to be logged in on this particular run. Reads Razorpay's own
    query-param names, since Payment Links append these automatically on redirect."""
    params = st.query_params
    plink_id = params.get("razorpay_payment_link_id")
    reference_id = params.get("razorpay_payment_link_reference_id", "")
    status = params.get("razorpay_payment_link_status")
    payment_id = params.get("razorpay_payment_id")
    signature = params.get("razorpay_signature")
    if not (plink_id and payment_id and signature and status):
        return
    if payment_already_verified(payment_id):
        st.query_params.clear()
        return
    if not razorpay_verify_payment_link_signature(plink_id, reference_id, status, payment_id, signature):
        st.query_params.clear()
        st.error("Payment verification failed — signature mismatch. If you were charged, "
                  "contact support with your payment ID: " + payment_id)
        return
    if status != "paid":
        st.query_params.clear()
        return
    owner = order_owner(plink_id)
    if owner is None:
        st.query_params.clear()
        st.error("Payment verified but no matching order was found. Contact support with "
                  "payment ID: " + payment_id)
        return
    if mark_order_paid(plink_id, payment_id):
        set_premium(owner["user_id"], True)
        st.query_params.clear()
        st.session_state.pop("premium_link_url", None)
        st.session_state.pop("premium_link_id", None)
        st.session_state["just_upgraded"] = True
        st.rerun()
    else:
        st.query_params.clear()


# ============================================================
# DASHBOARD EXTRAS — welcome hero + "today at a glance" snapshot
# ============================================================

STRENGTH_GRAHAS = ["Su", "Mo", "Ma", "Me", "Jp", "Ve", "Sa"]
DIGNITY_SCORE = {"Exalted": 100, "Own Sign": 80, "Neutral": 50, "Debilitated": 20}


def compute_planetary_strength_today(lat: float, lon: float, tz: float) -> dict:
    """A simplified, dignity-based strength proxy (0-100) for each of the 7
    classical grahas, using their CURRENT transiting sign — not a full
    classical Shadbala (six-fold strength) calculation, which also weighs
    positional/directional/temporal/motional/natural/aspectual strength well
    beyond sign dignity alone. Combust planets are docked 20 points."""
    now_local = now_in_city(tz)
    chart_today = compute_chart(
        now_local.year, now_local.month, now_local.day, now_local.hour, now_local.minute, lat, lon, tz
    )
    scores = {}
    for key in STRENGTH_GRAHAS:
        b = next(x for x in chart_today["bodies"] if x["key"] == key)
        dignity = graha_dignity(key, b["sign"])
        score = DIGNITY_SCORE[dignity]
        if b.get("combust"):
            score = max(0, score - 20)
        scores[key] = score
    return scores


def build_strength_radar_svg(scores: dict, size: int = 260) -> str:
    """A simple SVG radar/spider chart for the 7-graha strength scores, with
    each point's percentage labelled just outside the shape and the planet
    name pushed further out still, so the two never overlap."""
    cx = cy = size / 2
    r_max = size * 0.32
    n = len(STRENGTH_GRAHAS)
    parts = [f'<svg viewBox="0 0 {size} {size}" xmlns="http://www.w3.org/2000/svg" style="display:block;margin:0 auto;">']

    def pt(r, i):
        ang = math.radians(i * (360 / n) - 90)
        return cx + r * math.cos(ang), cy + r * math.sin(ang)

    for ring_frac in (0.33, 0.66, 1.0):
        ring_pts = [pt(r_max * ring_frac, i) for i in range(n)]
        pts_str = " ".join(f"{x:.1f},{y:.1f}" for x, y in ring_pts)
        parts.append(f'<polygon points="{pts_str}" fill="none" stroke="{C["line"]}" stroke-width="1"/>')
    for i in range(n):
        x, y = pt(r_max, i)
        parts.append(f'<line x1="{cx}" y1="{cy}" x2="{x:.1f}" y2="{y:.1f}" stroke="{C["line"]}" stroke-width="1"/>')
        lx, ly = pt(r_max + 30, i)
        parts.append(f'<text x="{lx:.1f}" y="{ly:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="12" font-weight="700" fill="{C["muted"]}" '
                      f'font-family="Georgia, serif">{STRENGTH_GRAHAS[i]}</text>')

    data_radii = [r_max * (scores[STRENGTH_GRAHAS[i]] / 100) for i in range(n)]
    data_pts = [pt(data_radii[i], i) for i in range(n)]
    data_str = " ".join(f"{x:.1f},{y:.1f}" for x, y in data_pts)
    parts.append(f'<polygon points="{data_str}" fill="{C["gold"]}" fill-opacity="0.28" '
                 f'stroke="{C["gold"]}" stroke-width="2"/>')
    for i, (x, y) in enumerate(data_pts):
        parts.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.5" fill="{C["gold"]}"/>')
        px, py = pt(data_radii[i] + 13, i)
        parts.append(f'<text x="{px:.1f}" y="{py:.1f}" text-anchor="middle" dominant-baseline="middle" '
                      f'font-size="9.5" font-weight="700" fill="{C["sindoor"]}" font-family="Georgia, serif">'
                      f'{scores[STRENGTH_GRAHAS[i]]}%</text>')

    parts.append("</svg>")
    return "".join(parts)


# ============================================================
# NUMEROLOGY — Pythagorean and Chaldean systems, kept strictly separate.
# ============================================================
# The two systems use DIFFERENT letter-to-number tables and different
# reduction conventions — this module never mixes a Pythagorean value into
# a Chaldean calculation or vice versa. Each computation function is
# explicitly named with its system so the caller can't accidentally cross
# them.

PYTHAGOREAN_LETTER_VALUES = {}
for _i, _letters in enumerate(["AJS", "BKT", "CLU", "DMV", "ENW", "FOX", "GPY", "HQZ", "IR"], start=1):
    for _ch in _letters:
        PYTHAGOREAN_LETTER_VALUES[_ch] = _i

# Chaldean deliberately has no letter mapped to 9 — in that tradition 9 is
# considered sacred/complete and is reserved for the results of a
# calculation, never assigned to a letter.
CHALDEAN_LETTER_VALUES = {}
for _i, _letters in enumerate(["AIJQY", "BKR", "CGLS", "DMT", "EHNX", "UVW", "OZ", "FP"], start=1):
    for _ch in _letters:
        CHALDEAN_LETTER_VALUES[_ch] = _i

VOWELS = set("AEIOU")
PYTHAGOREAN_MASTER_NUMBERS = {11, 22, 33}

NUMEROLOGY_MEANINGS_PYTHAGOREAN = {
    1: "Independence, leadership, initiative — the pioneer number.",
    2: "Cooperation, diplomacy, sensitivity — the peacemaker number.",
    3: "Creativity, self-expression, optimism — the communicator number.",
    4: "Discipline, stability, hard work — the builder number.",
    5: "Freedom, adaptability, change — the adventurer number.",
    6: "Responsibility, nurturing, harmony — the caretaker number.",
    7: "Introspection, analysis, spirituality — the seeker number.",
    8: "Ambition, authority, material success — the achiever number.",
    9: "Compassion, idealism, completion — the humanitarian number.",
    11: "Master number — intuition, inspiration, spiritual insight (a heightened 2).",
    22: "Master number — the 'master builder', large-scale practical vision (a heightened 4).",
    33: "Master number — the 'master teacher', selfless compassion on a grand scale (a heightened 6).",
}

# Chaldean interpretations are traditionally framed a bit differently —
# more fate/destiny-oriented, less about psychological traits — reflecting
# the system's different origin. Kept as separate text so nothing bleeds
# in from the Pythagorean meanings above.
NUMEROLOGY_MEANINGS_CHALDEAN = {
    1: "The Sun's number — authority, willpower, originality, a natural leader.",
    2: "The Moon's number — sensitivity, partnership, imagination, but can bring emotional swings.",
    3: "Jupiter's number — expansion, wisdom, good fortune, communication.",
    4: "Rahu's number — sudden change, rebellion against convention, unconventional paths.",
    5: "Mercury's number — versatility, quick thinking, business acumen, restlessness.",
    6: "Venus's number — beauty, love, harmony, artistic and domestic affairs.",
    7: "Ketu's number — introspection, mysticism, isolation, hidden depths.",
    8: "Saturn's number — karma, discipline, delay followed by hard-won reward, tests of patience.",
    9: "Mars's number — courage, energy, aggression, completion through struggle.",
}


def reduce_number(n: int, preserve_master: bool = False) -> int:
    """Digit-sums n down to a single digit. If preserve_master is True
    (Pythagorean convention), stops early at 11, 22, or 33. Chaldean
    calculations should call this with preserve_master=False, since that
    system doesn't treat those as special 'master' stopping points."""
    while n > 9:
        if preserve_master and n in PYTHAGOREAN_MASTER_NUMBERS:
            return n
        n = sum(int(d) for d in str(n))
    return n


def _clean_name(name: str) -> str:
    return "".join(ch for ch in name.upper() if ch.isalpha())


def pythagorean_life_path(dob: date) -> int:
    """Standard Pythagorean method: reduce month, day, and year separately
    (preserving master numbers at each step), then sum those three and
    reduce again."""
    m = reduce_number(dob.month, preserve_master=True)
    d = reduce_number(dob.day, preserve_master=True)
    y = reduce_number(dob.year, preserve_master=True)
    return reduce_number(m + d + y, preserve_master=True)


def pythagorean_expression(name: str) -> int:
    total = sum(PYTHAGOREAN_LETTER_VALUES.get(ch, 0) for ch in _clean_name(name))
    return reduce_number(total, preserve_master=True)


def pythagorean_soul_urge(name: str) -> int:
    total = sum(PYTHAGOREAN_LETTER_VALUES.get(ch, 0) for ch in _clean_name(name) if ch in VOWELS)
    return reduce_number(total, preserve_master=True)


def pythagorean_personality(name: str) -> int:
    total = sum(PYTHAGOREAN_LETTER_VALUES.get(ch, 0) for ch in _clean_name(name) if ch not in VOWELS)
    return reduce_number(total, preserve_master=True)


def pythagorean_birthday_number(dob: date) -> int:
    return reduce_number(dob.day, preserve_master=True)


def pythagorean_maturity(life_path: int, expression: int) -> int:
    return reduce_number(life_path + expression, preserve_master=True)


def pythagorean_personal_year(dob: date, year: int) -> int:
    m = reduce_number(dob.month, preserve_master=False)
    d = reduce_number(dob.day, preserve_master=False)
    y = reduce_number(year, preserve_master=False)
    return reduce_number(m + d + y, preserve_master=False)


def chaldean_life_number(dob: date) -> int:
    """Chaldean birth/life number: sum every digit of the full date and
    reduce fully to a single digit — this system doesn't preserve master
    numbers the way Pythagorean does."""
    digits = f"{dob.day}{dob.month}{dob.year}"
    total = sum(int(d) for d in digits)
    return reduce_number(total, preserve_master=False)


def chaldean_name_number(name: str) -> dict:
    """Chaldean tradition weighs both the unreduced 'compound number' (its
    own separate meaning, roughly in the 1-52 range for a typical name) and
    the final single-digit reduction — returns both."""
    total = sum(CHALDEAN_LETTER_VALUES.get(ch, 0) for ch in _clean_name(name))
    return {"compound": total, "reduced": reduce_number(total, preserve_master=False)}


KARMIC_DEBT_NUMBERS = {13, 14, 16, 19}
KARMIC_DEBT_MEANINGS = {
    13: "Traditionally linked to past avoidance of hard work — the lesson is disciplined, "
        "consistent effort rather than shortcuts.",
    14: "Traditionally linked to past misuse of freedom — the lesson is balance and "
        "moderation, especially around change and impulse.",
    16: "Traditionally linked to past pride or ego — the lesson is humility, often arriving "
        "through the unexpected collapse of something built on a shaky foundation.",
    19: "Traditionally linked to past misuse of power — the lesson is learning to stand "
        "independently while still cooperating with others.",
}


def _reduce_with_karmic_debt(n: int, preserve_master: bool = False):
    """Same as reduce_number, but also reports whether 13, 14, 16, or 19
    appeared as an intermediate sum along the way (a 'karmic debt' number,
    in Pythagorean tradition — flagged here as an interpretive note, not
    reduced away silently)."""
    debt = None
    while n > 9:
        if n in KARMIC_DEBT_NUMBERS:
            debt = n
        if preserve_master and n in PYTHAGOREAN_MASTER_NUMBERS:
            return n, debt
        n = sum(int(d) for d in str(n))
    return n, debt


def pythagorean_attitude(dob: date) -> int:
    """Birth month + birth day, reduced — the 'first reaction' number."""
    m = reduce_number(dob.month, preserve_master=True)
    d = reduce_number(dob.day, preserve_master=True)
    return reduce_number(m + d, preserve_master=True)


def pythagorean_balance(name: str) -> int:
    """From the FIRST letter of each name part (initials) — how someone
    tends to regain equilibrium under stress."""
    parts = [p for p in name.split() if p]
    total = sum(PYTHAGOREAN_LETTER_VALUES.get(p[0].upper(), 0) for p in parts if p[0].isalpha())
    return reduce_number(total, preserve_master=True) if total else 0


def pythagorean_hidden_passion(name: str) -> int:
    """The number (1-9) that occurs most often among all letters in the
    name — the standout natural talent that shows up repeatedly."""
    counts = {}
    for ch in _clean_name(name):
        v = PYTHAGOREAN_LETTER_VALUES.get(ch)
        if v:
            counts[v] = counts.get(v, 0) + 1
    if not counts:
        return 0
    return max(counts, key=lambda k: (counts[k], -k))


def pythagorean_karmic_lessons(name: str) -> list:
    """Numbers 1-9 that never appear at all among the name's letters —
    traditionally read as areas life will keep presenting lessons in."""
    present = {PYTHAGOREAN_LETTER_VALUES.get(ch) for ch in _clean_name(name)}
    return [n for n in range(1, 10) if n not in present]


def pythagorean_subconscious_self(name: str) -> int:
    """9 minus the count of karmic lesson numbers — classically read as how
    many of the 9 basic vibrations someone can instinctively draw on in a
    crisis (higher = more resourceful under pressure, by this tradition)."""
    return 9 - len(pythagorean_karmic_lessons(name))


def pythagorean_personal_month(dob: date, year: int, month: int) -> int:
    py = pythagorean_personal_year(dob, year)
    return reduce_number(py + reduce_number(month, preserve_master=False), preserve_master=False)


def pythagorean_personal_day(dob: date, year: int, month: int, day: int) -> int:
    pm = pythagorean_personal_month(dob, year, month)
    return reduce_number(pm + reduce_number(day, preserve_master=False), preserve_master=False)


LO_SHU_POSITIONS = {4: (0, 0), 9: (0, 1), 2: (0, 2), 3: (1, 0), 5: (1, 1),
                    7: (1, 2), 8: (2, 0), 1: (2, 1), 6: (2, 2)}
LO_SHU_ARROWS = {
    "Arrow of Determination": [4, 5, 6],
    "Arrow of Spirituality": [2, 5, 8],
    "Arrow of Intellect": [4, 9, 2],
    "Arrow of Emotional Balance": [3, 5, 7],
    "Arrow of Practicality": [8, 1, 6],
}


def compute_lo_shu_grid(dob: date) -> dict:
    """Populates the traditional 3x3 Lo Shu grid from every digit in the
    birth date, reports which cells are filled/missing/repeated, and checks
    the five commonly-discussed 'arrows' (lines of three all present, or
    all missing)."""
    digits = [int(d) for d in f"{dob.day}{dob.month}{dob.year}" if d != "0"]
    counts = {n: digits.count(n) for n in range(1, 10)}
    present = [n for n in range(1, 10) if counts[n] > 0]
    missing = [n for n in range(1, 10) if counts[n] == 0]
    repeated = [n for n in range(1, 10) if counts[n] > 1]
    arrows_present, arrows_missing = [], []
    for arrow_name, cells in LO_SHU_ARROWS.items():
        if all(counts[c] > 0 for c in cells):
            arrows_present.append(arrow_name)
        elif all(counts[c] == 0 for c in cells):
            arrows_missing.append(arrow_name)
    return {
        "counts": counts, "present": present, "missing": missing, "repeated": repeated,
        "arrows_present": arrows_present, "arrows_missing": arrows_missing,
    }


NUMEROLOGY_COMPAT_GROUPS = {
    1: {"harmonious": {1, 5, 7}, "friendly": {3, 9}, "challenging": {4, 8}},
    2: {"harmonious": {2, 4, 8}, "friendly": {6, 9}, "challenging": {1, 5}},
    3: {"harmonious": {3, 6, 9}, "friendly": {1, 5}, "challenging": {4, 7}},
    4: {"harmonious": {2, 4, 8}, "friendly": {7}, "challenging": {3, 5, 9}},
    5: {"harmonious": {1, 5, 7}, "friendly": {3}, "challenging": {2, 4}},
    6: {"harmonious": {3, 6, 9}, "friendly": {2}, "challenging": {5, 7}},
    7: {"harmonious": {1, 5, 7}, "friendly": {4}, "challenging": {3, 6, 8}},
    8: {"harmonious": {2, 4, 8}, "friendly": {6}, "challenging": {1, 9}},
    9: {"harmonious": {3, 6, 9}, "friendly": {1, 2}, "challenging": {4, 8}},
    11: {"harmonious": {2, 11, 22}, "friendly": {6, 9}, "challenging": {1, 8}},
    22: {"harmonious": {4, 11, 22}, "friendly": {2, 8}, "challenging": {5, 9}},
    33: {"harmonious": {6, 11, 22, 33}, "friendly": {3, 9}, "challenging": {8}},
}


def _pair_score(a: int, b: int) -> int:
    """0-100 interpretive closeness between two numerology numbers — this
    scoring is an editorial construct of this application, not a
    standardized numerological formula."""
    a_r = a if a in NUMEROLOGY_COMPAT_GROUPS else reduce_number(a, preserve_master=True)
    b_r = b if b in NUMEROLOGY_COMPAT_GROUPS else reduce_number(b, preserve_master=True)
    if a_r == b_r:
        return 90
    groups_a = NUMEROLOGY_COMPAT_GROUPS.get(a_r, {"harmonious": set(), "friendly": set(), "challenging": set()})
    if b_r in groups_a["harmonious"]:
        return 82
    if b_r in groups_a["friendly"]:
        return 65
    if b_r in groups_a["challenging"]:
        return 35
    return 55


def compute_numerology_compatibility(name_a: str, dob_a: date, name_b: str, dob_b: date) -> dict:
    """Compares two people across Life Path, Expression, Soul Urge,
    Personality, and Birthday Number (Pythagorean throughout — this
    comparison isn't run in Chaldean, to avoid mixing systems), producing an
    overall interpretive score plus category breakdowns. This score is
    generated by this application's own weighting, not a scientifically
    validated measurement."""
    a = {
        "life_path": pythagorean_life_path(dob_a), "expression": pythagorean_expression(name_a),
        "soul_urge": pythagorean_soul_urge(name_a), "personality": pythagorean_personality(name_a),
        "birthday": pythagorean_birthday_number(dob_a),
    }
    b = {
        "life_path": pythagorean_life_path(dob_b), "expression": pythagorean_expression(name_b),
        "soul_urge": pythagorean_soul_urge(name_b), "personality": pythagorean_personality(name_b),
        "birthday": pythagorean_birthday_number(dob_b),
    }
    scores = {k: _pair_score(a[k], b[k]) for k in a}
    overall = round(
        scores["life_path"] * 0.30 + scores["expression"] * 0.20 + scores["soul_urge"] * 0.25 +
        scores["personality"] * 0.15 + scores["birthday"] * 0.10
    )
    if overall <= 30:
        band = "Challenging"
    elif overall <= 50:
        band = "Moderate"
    elif overall <= 70:
        band = "Good"
    elif overall <= 85:
        band = "Strong"
    else:
        band = "Highly compatible"
    categories = {
        "❤️ Love Compatibility": round(scores["soul_urge"] * 0.6 + scores["life_path"] * 0.4),
        "💬 Communication": round(scores["expression"] * 0.6 + scores["personality"] * 0.4),
        "💰 Financial Compatibility": round(scores["life_path"] * 0.5 + scores["expression"] * 0.5),
        "🤝 Friendship": round(scores["personality"] * 0.5 + scores["soul_urge"] * 0.5),
        "💍 Long-Term Potential": round(scores["life_path"] * 0.5 + scores["birthday"] * 0.5),
        "🔥 Attraction": round(scores["soul_urge"] * 0.7 + scores["personality"] * 0.3),
        "🧠 Mental Compatibility": round(scores["expression"] * 0.5 + scores["life_path"] * 0.5),
    }
    return {"a": a, "b": b, "scores": scores, "overall": overall, "band": band, "categories": categories}


def render_dashboard_hero(username: str, saved_profile):
    """Hero banner: a compact, top-to-bottom birth-details form on the left
    (Name, Date, Time, Place, Cast chart, Save chart) so entering details is
    the very first thing on the page, with the solar-system graphic on the
    right for the same visual identity as the login page. Returns the
    collected form values (name, dob, tob, city, cast, save_clicked,
    save_label) for the rest of the page to use — the actual chart results
    render further down, so entering details here means scrolling down to
    see them, same flow as before, just with the form moved to the top."""
    solar_svg = build_planetspath_solar_svg(480)
    st.markdown(
        f"""
        <style>
        .hero-form-wrap {{ position:relative; background:{C['panel']}; border:1px solid {C['line']};
            border-radius:18px; padding:20px 24px; margin-bottom:16px; overflow:hidden; }}
        </style>
        <div class="hero-form-wrap">
        """,
        unsafe_allow_html=True,
    )
    hero_l, hero_r = st.columns([1, 1.1])

    _load = st.session_state.pop("_load_chart_override", None)
    if _load:
        # Guaranteed-reliable way to programmatically set a Streamlit widget's
        # value: write directly to session_state[key] BEFORE that widget is
        # instantiated. Forces "Enter coordinates manually" so the loaded
        # chart's exact saved lat/lon/tz is restored precisely, rather than
        # trying to reverse-engineer a matching quick-pick city or search query.
        st.session_state["hero_name"] = _load["name"]
        st.session_state["hero_gender"] = _load.get("gender") if _load.get("gender") in ("Male", "Female") else "Male"
        st.session_state["hero_dob"] = _load["dob"]
        st.session_state["tob_hour"] = _load["tob"].hour
        st.session_state["tob_minute"] = _load["tob"].minute
        st.session_state["tob_second"] = _load["tob"].second
        st.session_state["hero_place_mode"] = "Enter coordinates manually"
        st.session_state["hero_manual_place_name"] = _load["city"][0]
        st.session_state["hero_manual_lat"] = float(_load["city"][2])
        st.session_state["hero_manual_lon"] = float(_load["city"][3])
        st.session_state["hero_manual_tz"] = float(_load["city"][4])
        st.session_state["_just_loaded_chart"] = True
        st.success(f"Loaded \u201c{_load['label']}\u201d \u2014 scroll down to see the chart.")

    with hero_l:
        st.markdown(f'<h4 style="margin-bottom:10px;">Birth Details</h4>', unsafe_allow_html=True)
        default_name = saved_profile["name"] if saved_profile else ""
        name = st.text_input("Name", value=default_name, placeholder="Name of chart", key="hero_name")

        gender_options = ["Male", "Female"]
        default_gender = saved_profile.get("gender") if saved_profile else None
        gender_index = gender_options.index(default_gender) if default_gender in gender_options else 0
        gender = st.radio("Gender", gender_options, index=gender_index, horizontal=True, key="hero_gender")

        default_dob = date.fromisoformat(saved_profile["dob"]) if (saved_profile and saved_profile.get("dob")) else date(2026, 7, 16)
        dob = st.date_input(
            "Date of birth", value=default_dob,
            min_value=date(1900, 1, 1), max_value=date(2100, 12, 31), key="hero_dob",
        )

        default_tob = dtime.fromisoformat(saved_profile["tob"]) if (saved_profile and saved_profile.get("tob")) else dtime(12, 16, 0)
        st.markdown('<p style="margin-bottom:2px;">Time of birth (24h, local)</p>', unsafe_allow_html=True)
        th_col, tm_col, ts_col = st.columns(3)
        with th_col:
            tob_hour = st.number_input("Hour", min_value=0, max_value=23, value=default_tob.hour, step=1, key="tob_hour")
        with tm_col:
            tob_minute = st.number_input("Minute", min_value=0, max_value=59, value=default_tob.minute, step=1, key="tob_minute")
        with ts_col:
            tob_second = st.number_input("Second", min_value=0, max_value=59, value=default_tob.second, step=1, key="tob_second")
        tob = dtime(int(tob_hour), int(tob_minute), int(tob_second))

        place_mode = st.radio(
            "Birth place source",
            ["Quick-pick from city list", "Search worldwide (any place)", "Enter coordinates manually"],
            key="hero_place_mode",
        )

        if place_mode == "Enter coordinates manually":
            default_place = saved_profile["city_name"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else ""
            default_mlat = saved_profile["lat"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 30.21
            default_mlon = saved_profile["lon"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 74.95
            default_mtz = saved_profile["tz"] if (saved_profile and saved_profile.get("city_region") == "Manual entry") else 5.5
            place_name = st.text_input("Place name (for display only)", value=default_place, placeholder="e.g. Custom Town", key="hero_manual_place_name")
            manual_lat = st.number_input("Latitude", min_value=-90.0, max_value=90.0, value=float(default_mlat), step=0.0001, format="%.4f", key="hero_manual_lat")
            manual_lon = st.number_input("Longitude", min_value=-180.0, max_value=180.0, value=float(default_mlon), step=0.0001, format="%.4f", key="hero_manual_lon")
            manual_tz = st.number_input("UTC offset (h)", min_value=-12.0, max_value=14.0, value=float(default_mtz), step=0.25, format="%.2f", key="hero_manual_tz")
            st.caption(
                f"{abs(manual_lat):.4f}°{'N' if manual_lat >= 0 else 'S'}, "
                f"{abs(manual_lon):.4f}°{'E' if manual_lon >= 0 else 'W'} · "
                f"UTC{'+' if manual_tz >= 0 else ''}{manual_tz}"
            )
            city = (place_name if place_name else "Custom location", "Manual entry", manual_lat, manual_lon, manual_tz)

        elif place_mode == "Search worldwide (any place)":
            default_query = saved_profile["city_name"] if (saved_profile and saved_profile.get("city_region") == "Worldwide search") else ""
            search_query = st.text_input(
                "Birth place (any city, town, or village worldwide)",
                value=default_query, placeholder="e.g. Hanumangarh, Rajasthan, India",
            )
            results = geocode_place(search_query) if search_query.strip() else []
            if search_query.strip() and not results:
                st.caption("No matches found — try a more specific query, or use Quick-pick / manual entry instead.")
            if results:
                result_labels = [r["display_name"] for r in results]
                chosen_result_label = st.selectbox("Match", result_labels, label_visibility="collapsed")
                chosen_result = results[result_labels.index(chosen_result_label)]
                w_lat, w_lon = chosen_result["lat"], chosen_result["lon"]
                w_tz = get_historical_utc_offset(w_lat, w_lon, dob.year, dob.month, dob.day, tob.hour, tob.minute, tob.second)
                display_name = chosen_result["display_name"]
                st.caption(
                    f"{abs(w_lat):.4f}°{'N' if w_lat >= 0 else 'S'}, "
                    f"{abs(w_lon):.4f}°{'E' if w_lon >= 0 else 'W'} · UTC{'+' if w_tz >= 0 else ''}{w_tz:.2f} on this date"
                )
                city = (display_name.split(",")[0].strip(), display_name, w_lat, w_lon, w_tz)
            else:
                city = ("Bathinda", "Punjab, India", 30.21, 74.95, 5.5)

        else:
            default_city_query = saved_profile["city_name"] if (saved_profile and saved_profile.get("city_region") not in ("Manual entry", "Worldwide search")) else "Bathinda"
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

        cast = st.button("📊 Chart", use_container_width=True)

        save_label = st.text_input("Label to save this chart as", value=(name or "Untitled chart"), key="hero_save_label")
        save_clicked = st.button("💾 Save Chart", use_container_width=True)

    with hero_r:
        st.markdown(f'<div style="max-width:560px;margin:20px auto 0;">{solar_svg}</div>', unsafe_allow_html=True)

    st.markdown("</div>", unsafe_allow_html=True)
    return name, gender, dob, tob, city, cast, save_clicked, save_label


def render_todays_snapshot(lat: float, lon: float, tz: float, city_name: str):
    """Four 'at a glance' cards for TODAY (not the birth date) — distinct from
    the birth-chart-specific content below: today's Panchang, today's
    auspicious/inauspicious windows, today's day-wise remedy, and a
    simplified planetary strength radar."""
    now_local = now_in_city(tz)
    today_chart = compute_chart(now_local.year, now_local.month, now_local.day,
                                 now_local.hour, now_local.minute, lat, lon, tz)
    today_pan = today_chart["panchanga"]
    today_mw = compute_muhurta_windows(now_local.year, now_local.month, now_local.day, lat, lon, tz)
    today_idx = date.today().isoweekday() % 7
    day_name, day_key, gem, colour, remedy = DAY_REMEDIES[today_idx]
    strength_scores = compute_planetary_strength_today(lat, lon, tz)

    sc1, sc2, sc3, sc4 = st.columns(4)
    with sc1:
        st.markdown(
            f'<div class="kcard" style="min-height:190px;"><h4 style="font-size:14px;">Today\'s Panchāṅga</h4>'
            f'<div class="krow" style="font-size:14px;"><span class="kmuted">Tithi</span>'
            f'<span>{today_pan["paksha"]} {today_pan["tithiName"]}</span></div>'
            f'<div class="krow" style="font-size:14px;"><span class="kmuted">Nakṣatra</span>'
            f'<span>{NAKSHATRAS[today_pan["nakIdx"]]}</span></div>'
            f'<div class="krow" style="font-size:14px;"><span class="kmuted">Yoga</span>'
            f'<span>{YOGAS[today_pan["yogaIdx"]]}</span></div>'
            f'<div class="krow" style="font-size:14px;border-bottom:none;"><span class="kmuted">Karaṇa</span>'
            f'<span>{today_pan["karana"]}</span></div></div>',
            unsafe_allow_html=True,
        )
    with sc2:
        st.markdown(
            f'<div class="kcard" style="min-height:190px;"><h4 style="font-size:14px;">Auspicious Timings</h4>'
            f'<div class="krow" style="font-size:13px;"><span class="ksindoor">Abhijit</span>'
            f'<span class="ksindoor">{_fmt_hm(today_mw["abhijit"][0])}\u2013{_fmt_hm(today_mw["abhijit"][1])}</span></div>'
            f'<div class="krow" style="font-size:13px;"><span class="kmuted">Rāhu Kālam</span>'
            f'<span class="kmuted">{_fmt_hm(today_mw["rahu_kalam"][0])}\u2013{_fmt_hm(today_mw["rahu_kalam"][1])}</span></div>'
            f'<div class="krow" style="font-size:13px;"><span class="kmuted">Yamaganda</span>'
            f'<span class="kmuted">{_fmt_hm(today_mw["yamaganda"][0])}\u2013{_fmt_hm(today_mw["yamaganda"][1])}</span></div>'
            f'<div class="krow" style="font-size:13px;border-bottom:none;"><span class="kmuted">Gulika</span>'
            f'<span class="kmuted">{_fmt_hm(today_mw["gulika_kalam"][0])}\u2013{_fmt_hm(today_mw["gulika_kalam"][1])}</span></div></div>',
            unsafe_allow_html=True,
        )
    with sc3:
        st.markdown(
            f'<div class="kcard" style="min-height:190px;"><h4 style="font-size:14px;">Today\'s Remedy</h4>'
            f'<p style="font-size:13px;margin:4px 0;"><b>{day_name}</b> \u00b7 ruled by {BODY_FULLNAME_ASCII.get(day_key, day_key)}</p>'
            f'<p class="kmuted" style="font-size:12.5px;margin:6px 0;">Gemstone: {gem} \u00b7 Colour: {colour}</p>'
            f'<p style="font-size:13px;margin:6px 0;">{remedy}</p></div>',
            unsafe_allow_html=True,
        )
    with sc4:
        radar_svg = build_strength_radar_svg(strength_scores, 240)
        st.markdown(
            f'<div class="kcard" style="min-height:190px;text-align:center;">'
            f'<h4 style="font-size:14px;">Planetary Strength</h4>{radar_svg}</div>',
            unsafe_allow_html=True,
        )
    st.caption(
        f"\u2139\ufe0f Snapshot for {city_name}, as of {now_local.strftime('%d %b %Y, %H:%M')}. "
        "Planetary Strength is a simplified sign-dignity indicator, not a full classical Shadbala calculation."
    )


DASHBOARD_HUB_CARDS = [
    ("\U0001f504", "Nakshatra Live & Transits", "See today's tithi, nakshatra, and live planetary positions.",
     "#section-transit", "#E3F2FD", "#1565C0"),
    ("\U0001f4ff", "Day-wise Remedies", "Gemstones, colours, and practices for each weekday.",
     "#section-remedies", "#E8F5E9", "#2E7D32"),
    ("\U0001f319", "Navtara Chakra", "Your auspicious-day calendar, based on your own nakshatra.",
     "#section-navtara", "#F3E5F5", "#6A1B9A"),
    ("\U0001f549\ufe0f", "Panchang & Muhurta", "Daily panchang, hora timings, and auspicious windows.",
     "#section-muhurta", "#FFF8E1", "#B8860B"),
    ("\U0001f49e", "Compatibility", "Match your kundali against a partner's, graha by graha.",
     "#section-compat", "#FCE4EC", "#AD1457"),
    ("\U0001f4c1", "Charts", "Your saved birth charts — load, revisit, or delete any of them.",
     "#section-charts", "#FFF3E0", "#E65100"),
    ("\U0001f522", "Numerology", "Life Path, Destiny, Soul Urge, and more — Pythagorean and Chaldean.",
     "#section-numerology", "#E0F7FA", "#00695C"),
]


def render_dashboard_hub():
    """A visual, card-based home for the dashboard — click any card to jump
    straight to that section (same anchors the top nav bar already uses),
    just presented as an inviting light-coloured grid instead of plain text
    links. Built as an HTML table rather than CSS grid/flex, since this
    codebase found CSS grid unreliable across renderers earlier and a table
    is guaranteed to lay out identically everywhere."""
    st.markdown(f'<p style="color:{C["gold"]};font-weight:700;font-size:19px;margin:4px 0 10px;">\u2728 Your Dashboard</p>', unsafe_allow_html=True)

    def _hub_card(icon, title, desc, href, bg, fg):
        return (
            f'<td style="width:25%;padding:7px;vertical-align:top;">'
            f'<a href="{href}" style="text-decoration:none;">'
            f'<div style="background:{bg}; border:1px solid {fg}33; border-radius:16px; padding:18px 16px; '
            f'min-height:128px; transition:transform 0.15s;">'
            f'<div style="font-size:30px;margin-bottom:8px;">{icon}</div>'
            f'<div style="font-weight:700; color:{fg}; font-size:15px; margin-bottom:4px;">{title}</div>'
            f'<div style="color:{fg}cc; font-size:12.5px; line-height:1.4;">{desc}</div>'
            f'</div></a></td>'
        )

    cards = DASHBOARD_HUB_CARDS
    rows_html = []
    for i in range(0, len(cards), 4):
        row_cards = cards[i:i + 4]
        row_html = "".join(_hub_card(*c) for c in row_cards)
        if len(row_cards) < 4:
            row_html += '<td style="width:25%;"></td>' * (4 - len(row_cards))
        rows_html.append(f"<tr>{row_html}</tr>")

    st.markdown(
        f'<table style="width:100%; border-collapse:separate; border-spacing:0; margin-bottom:18px;">'
        f'{"".join(rows_html)}</table>',
        unsafe_allow_html=True,
    )


def render_nakshatra_live_clock(lat: float, lon: float, tz: float):
    """A self-updating 'live clock' card: current tithi, current nakshatra
    with its 4 padas, and a live-ticking indicator of which pada is active
    right now. The Python side computes real boundary timestamps (via the
    app's own ephemeris — no hardcoded date window, works for any day);
    a small client-side script then just interpolates the current moment
    against those real boundaries once a second, so the display stays live
    without repeated server round-trips."""
    data = compute_nakshatra_live_data(lat, lon, tz)
    if not data.get("ok"):
        st.info("Live nakshatra clock is temporarily unavailable for this location/time.")
        return

    import json as _json
    data_json = _json.dumps(data)
    planet_colors_json = _json.dumps(PLANET_TRANSIT_COLORS)

    html = f"""
    <div style="font-family:Georgia,'Times New Roman',serif;">
    <div id="nak-live"></div>
    </div>
    <script>
    (function() {{
        var DATA = {data_json};
        var COLORS = {planet_colors_json};
        function hexFg(hex) {{ return hex; }}
        function bgTint(hex) {{
            var r = parseInt(hex.slice(1,3),16), g = parseInt(hex.slice(3,5),16), b = parseInt(hex.slice(5,7),16);
            return 'rgba(' + r + ',' + g + ',' + b + ',0.16)';
        }}
        var THEME_BG = '#FFF3B0';
        var THEME_BG_SOFT = '#FFF9C4';
        var THEME_ACCENT = '#B8842E';
        var THEME_TEXT = '#3A2E1F';
        var THEME_MUTED = '#7A6F5C';
        function dm(deg) {{
            var d = Math.floor(deg), m = Math.round((deg - d) * 60);
            if (m === 60) {{ d += 1; m = 0; }}
            return d + '\\u00b0' + (m < 10 ? '0' : '') + m + "'";
        }}
        function moonSvg(size, light, dark) {{
            return '<svg width="' + size + '" height="' + size + '" viewBox="0 0 24 24">' +
              '<circle cx="12" cy="12" r="11" fill="' + light + '"/>' +
              '<path d="M12 1a11 11 0 0 1 0 22 8.5 11 0 0 0 0-22Z" fill="' + dark + '"/></svg>';
        }}
        function render() {{
            var now = new Date();
            var out = document.getElementById('nak-live');
            var fmt = {{ hour:'numeric', minute:'2-digit', second:'2-digit' }};
            var fmtNow = {{ weekday:'long', month:'short', day:'numeric', hour:'numeric', minute:'2-digit', second:'2-digit' }};
            var nowLine = '<div style="font-size:16px;color:' + THEME_MUTED + ';margin-bottom:16px;font-family:Arial,sans-serif;">' +
                now.toLocaleString('en-US', fmtNow) + ' &middot; updates live</div>';

            var isKrishna = DATA.paksha === 'Krishna';
            var tithiHtml = '';
            if (DATA.tithi_start_iso && DATA.tithi_end_iso) {{
                var ts = new Date(DATA.tithi_start_iso), te = new Date(DATA.tithi_end_iso);
                var frac = Math.min(1, Math.max(0, (now - ts) / (te - ts)));
                var illum = Math.round(frac * 100);
                tithiHtml = '<div style="display:flex;align-items:center;gap:16px;border-radius:12px;' +
                  'padding:16px 20px;margin-bottom:18px;background:' + THEME_BG_SOFT + ';border:1px solid ' + THEME_BG + ';">' +
                  '<div>' + moonSvg(40, THEME_BG, THEME_ACCENT) + '</div>' +
                  '<div><div style="font-size:21px;font-weight:700;color:' + THEME_TEXT + ';">' + DATA.tithi_name + '</div>' +
                  '<div style="font-size:15px;color:' + THEME_MUTED + ';margin-top:2px;font-family:Arial,sans-serif;">' +
                  DATA.paksha + ' Paksha</div></div>' +
                  '<div style="margin-left:auto;text-align:right;font-size:15px;color:' + THEME_MUTED + ';font-family:Arial,sans-serif;">' +
                  '<span style="font-size:24px;font-weight:700;color:' + THEME_TEXT + ';display:block;">' + illum + '%</span>elapsed</div></div>';
            }}

            var ns = new Date(DATA.nak_start_iso), ne = new Date(DATA.nak_end_iso);
            var quarterMs = (ne - ns) / 4;
            var padaIdx = Math.min(3, Math.max(0, Math.floor((now - ns) / quarterMs)));
            var padaEnd = new Date(ns.getTime() + (padaIdx + 1) * quarterMs);
            var padasHtml = DATA.padas.map(function(p, i) {{
                var cur = i === padaIdx;
                var pStart = new Date(p.start_iso), pEnd = new Date(p.end_iso);
                return '<td style="width:25%;padding:0 6px;vertical-align:top;"><div style="border-radius:12px;padding:16px;position:relative;' +
                  'opacity:' + (cur ? '1' : '0.7') + ';background:' + (cur ? THEME_BG : THEME_BG_SOFT) +
                  (cur ? ';border:2px solid ' + THEME_ACCENT : ';border:2px solid transparent') + ';">' +
                  (cur ? '<div style="position:absolute;top:10px;right:10px;">' + moonSvg(20, '#fff', THEME_ACCENT) + '</div>' : '') +
                  '<div style="font-size:13px;text-transform:uppercase;color:' + THEME_ACCENT + ';font-family:Arial,sans-serif;font-weight:700;">Pada ' + (i+1) + (cur ? ' &middot; now' : '') + '</div>' +
                  '<div style="font-size:19px;font-weight:700;margin:6px 0;color:' + THEME_TEXT + ';">' + p.sign + '</div>' +
                  '<div style="font-size:13px;opacity:0.85;margin-bottom:4px;color:' + THEME_MUTED + ';font-family:Arial,sans-serif;">Ruled by ' + p.lord + '</div>' +
                  '<div style="font-size:13.5px;color:' + THEME_MUTED + ';font-family:Arial,sans-serif;">' + dm(p.deg_start) + '\\u2013' + dm(p.deg_end) + '</div>' +
                  '<div style="font-size:13.5px;color:' + THEME_MUTED + ';font-family:Arial,sans-serif;">' + pStart.toLocaleTimeString('en-US', fmt) + '\\u2013' + pEnd.toLocaleTimeString('en-US', fmt) + '</div>' +
                  '</div></td>';
            }}).join('');

            out.innerHTML = nowLine + tithiHtml +
              '<div style="display:inline-block;border-radius:12px;padding:18px 26px;margin-bottom:12px;' +
              'font-size:34px;font-weight:700;background:' + THEME_BG + ';color:' + THEME_TEXT + ';">' + DATA.nakshatra + '</div><br>' +
              '<span style="display:inline-block;font-size:15px;padding:6px 16px;border-radius:8px;' +
              'background:' + THEME_BG_SOFT + ';border:1px solid ' + THEME_BG + ';color:' + THEME_TEXT + ';font-family:Arial,sans-serif;">Nakshatra ' + DATA.nak_num +
              ' / 27 &middot; ' + DATA.rashi + ' ' + dm(DATA.deg_start) + '\\u2013' + dm(DATA.deg_end) + ' &middot; lord ' + DATA.lord + '</span>' +
              '<table style="width:100%;border-collapse:separate;border-spacing:0;margin:18px 0;table-layout:fixed;"><tr>' + padasHtml + '</tr></table>' +
              '<div style="font-size:15px;color:' + THEME_MUTED + ';margin-top:8px;line-height:1.65;font-family:Arial,sans-serif;">' +
              'Currently in pada ' + (padaIdx+1) + ', running until ' + padaEnd.toLocaleTimeString('en-US', fmt) +
              '. Presided over by ' + DATA.deity + '. Traits: ' + DATA.traits + '.</div>';
        }}
        render();
        setInterval(render, 1000);
    }})();
    </script>
    """
    st.components.v1.html(html, height=470, scrolling=False)


# ============================================================
# STREAMLIT APP
# ============================================================

st.set_page_config(
    page_title="Kuṇḍalī", page_icon="✨", layout="wide",
    menu_items={"Get Help": None, "Report a bug": None, "About": None},
)

st.markdown(
    f"""
    <style>
    /* Hide Streamlit's own chrome for a clean, professional look:
       main hamburger menu, "Deploy" button, footer, and the
       "Hosted with Streamlit" badge in the bottom-right corner. */
    #MainMenu {{ visibility: hidden; }}
    header[data-testid="stHeader"] {{ display: none; }}
    footer {{ display: none; }}
    .stAppDeployButton {{ display: none; }}
    div[data-testid="stStatusWidget"] {{ visibility: hidden; }}
    a[href*="streamlit.io"] {{ display: none !important; }}
    .block-container {{ padding-top: 1rem !important; }}

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
    .gtable {{ width: 100%; border-collapse: collapse; font-size: 19px; }}
    .gtable th {{
        text-align: left; color: {C["gold"]}; font-weight: 700;
        padding: 10px 14px; border-bottom: 2px solid {C["line"]}; white-space: nowrap;
    }}
    .gtable td {{ padding: 11px 14px; border-bottom: 1px solid {C["line"]}; white-space: nowrap; }}
    .gtable tr:nth-child(even) {{ background: {C["panelSoft"]}; }}
    .gtable .lord {{ color: {C["sindoor"]}; font-weight: 600; }}
    .gtable .body-key {{ font-weight: 700; color: {C["sindoor"]}; }}
    .gtable th.uh {{ text-decoration: underline; }}
    </style>
    """,
    unsafe_allow_html=True,
)

# ---- Auth gate: nothing below runs until the person is logged in ----------
# A direct "?preview=1" link auto-signs in as the fixed demo account above —
# handy for a payment-gateway reviewer who'd rather click a link than type
# credentials. Regular visitors without that query param still see the normal
# login/signup screen; nothing about the auth flow itself changes.
if "user" not in st.session_state and st.query_params.get("preview") == "1":
    demo_user, _ = authenticate(DEMO_USERNAME, DEMO_PASSWORD)
    if demo_user:
        st.session_state["user"] = {"id": demo_user["id"], "username": demo_user["username"]}
        st.rerun()

# "Remember me": a valid, unexpired token in the URL (?rt=...) signs the
# person straight back in without re-entering credentials, for up to
# REMEMBER_ME_DAYS after they last checked the box — this is what lets
# sign-in survive closing the browser entirely, not just staying on the tab.
if "user" not in st.session_state:
    rt = st.query_params.get("rt")
    if rt:
        rt_user = validate_remember_token(rt)
        if rt_user:
            st.session_state["user"] = {"id": rt_user["id"], "username": rt_user["username"]}
            st.rerun()

if "user" not in st.session_state:
    render_auth_screen()
    st.stop()

_goto = st.query_params.get("goto")
if _goto:
    st.session_state["_scroll_to_section"] = _goto
    st.query_params.pop("goto", None)

handle_razorpay_return()
if st.session_state.pop("just_upgraded", False):
    st.success("Payment verified — premium unlocked! 🎉")

st.markdown(
    f'<p style="font-family:Georgia,serif; font-style:italic; color:{C["muted"]}; '
    f'font-size:14px; text-align:center; margin:0 0 10px;">'
    f'The planets move in their path, and so does your destiny.</p>',
    unsafe_allow_html=True,
)

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
        rt_to_revoke = st.query_params.get("rt")
        if rt_to_revoke:
            revoke_remember_token(rt_to_revoke)
            st.query_params.pop("rt", None)
        del st.session_state["user"]
        st.session_state.pop("form", None)
        st.rerun()

_dash_profile = load_profile(st.session_state["user"]["id"])
if _dash_profile and _dash_profile.get("lat") is not None:
    _dash_lat, _dash_lon, _dash_tz, _dash_city = (
        _dash_profile["lat"], _dash_profile["lon"], _dash_profile["tz"], _dash_profile["city_name"],
    )
else:
    _dash_lat, _dash_lon, _dash_tz, _dash_city = 30.21, 74.95, 5.5, "Bathinda"

if is_premium(st.session_state["user"]["id"]):
    st.markdown(
        f"""
        <style>
        .section-nav {{
            position: sticky; top: 0; z-index: 999;
            background: {C['panel']}; border: 1px solid {C['line']}; border-radius: 14px;
            padding: 12px 20px; margin-bottom: 18px; box-shadow: 0 2px 10px rgba(58,46,31,0.08);
            display: flex; gap: 8px; flex-wrap: wrap; justify-content: center;
        }}
        .section-nav a {{
            color: {C['ivory']}; text-decoration: none; font-size: 17px; font-weight: 700;
            padding: 8px 18px; border-radius: 22px; border: 1px solid transparent;
            transition: all 0.15s ease; white-space: nowrap;
        }}
        .section-nav a:hover {{
            background: {C['panelSoft']}; border-color: {C['gold']}; color: {C['gold']};
        }}
        </style>
        <div class="section-nav">
            <a href="#section-transit">🔄 Nakshatra Live &amp; Current Transits</a>
            <a href="#section-remedies">📿 Day-wise Remedies</a>
            <a href="#section-navtara">🌙 Navtara Chakra</a>
            <a href="#section-muhurta">🕉️ Panchang &amp; Muhurta</a>
            <a href="#section-compat">💞 Compatibility</a>
            <a href="#section-charts">📁 Charts</a>
            <a href="#section-numerology">🔢 Numerology</a>
        </div>
        """,
        unsafe_allow_html=True,
    )

saved_profile = load_profile(st.session_state["user"]["id"])
name, gender, dob, tob, city, cast, save_clicked, save_label = render_dashboard_hero(
    st.session_state["user"]["username"], saved_profile
)
if save_clicked:
    save_chart_to_library(
        st.session_state["user"]["id"], save_label.strip() or "Untitled chart", name,
        dob.isoformat(), tob.isoformat(), city[0], city[1], city[2], city[3], city[4],
    )
    st.success(f"Saved \u201c{save_label.strip() or 'Untitled chart'}\u201d to your chart library.")
render_todays_snapshot(_dash_lat, _dash_lon, _dash_tz, _dash_city)


if PAYMENT_TEST_MODE:
    st.markdown(
        '<div style="background:#FCE8E6;border:1px solid #D93025;border-radius:8px;'
        'padding:8px 16px;margin-bottom:14px;color:#D93025;font-size:14px;font-weight:600;">'
        '\U0001f9ea TEST MODE \u2014 payments are simulated. No real money moves. '
        'Add real Razorpay keys (RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET, APP_BASE_URL) to go live.'
        '</div>',
        unsafe_allow_html=True,
    )

# ---- Free-tier daily chart-generation limit --------------------------------
_user_id_for_limit = st.session_state["user"]["id"]
_premium_for_limit = is_premium(_user_id_for_limit)
_today_usage = 0 if _premium_for_limit else get_today_usage_count(_user_id_for_limit)
_limit_reached = (not _premium_for_limit) and _today_usage >= FREE_DAILY_LIMIT

if not _premium_for_limit:
    st.caption(
        f"🔢 Free plan: {max(0, FREE_DAILY_LIMIT - _today_usage)} of {FREE_DAILY_LIMIT} "
        "chart generations left today. Premium accounts are unlimited."
    )

# Keep last-cast form in session_state so the chart persists across reruns
_just_loaded = st.session_state.pop("_just_loaded_chart", False)
_want_new_chart = "form" not in st.session_state or cast or _just_loaded
if _want_new_chart and _limit_reached and not _just_loaded:
    st.warning(
        f"⭐ You've used all {FREE_DAILY_LIMIT} free chart generations for today. "
        "Upgrade to Premium below for unlimited charts, or come back tomorrow."
    )
    if "form" not in st.session_state:
        # Fresh browser session (new tab/refresh) with the limit already used up —
        # there's nothing cached to fall back to, so still populate the current
        # widget values so something renders, but WITHOUT counting it as a new
        # generation (no increment_usage call here, unlike the branch below).
        st.session_state["form"] = {
            "name": name, "gender": gender, "dob": dob, "tob": tob, "city": city,
        }
elif _want_new_chart:
    st.session_state["form"] = {
        "name": name, "gender": gender, "dob": dob, "tob": tob, "city": city,
    }
    if cast:
        save_profile(
            st.session_state["user"]["id"], name, dob.isoformat(), tob.isoformat(),
            city[0], city[1], city[2], city[3], city[4], gender,
        )
    if cast and not _premium_for_limit:
        increment_usage(_user_id_for_limit)
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

# ---- Chart display toggles: read the current (prior-run) values now so
# they affect this run's chart rendering; the actual widgets are drawn below
# the charts, per the requested "options at the bottom" placement. Streamlit
# preserves widget values in session_state across reruns by key, so reading
# them here before the widgets are instantiated further down still reflects
# the user's last choice.
_chart_show_nak = st.session_state.get("chart_show_nakshatra", True)
_chart_language = st.session_state.get("chart_language", "English")
_chart_show_transits = st.session_state.get("chart_show_transits", True)

# ---- Row 1: Diamond chart + Circular chart, each with its own D1..D60 selector ----
st.markdown('<div id="main-kundali-chart"></div>', unsafe_allow_html=True)
if _just_loaded:
    st.components.v1.html(
        """<script>
        window.parent.document.getElementById('main-kundali-chart')
            .scrollIntoView({behavior: 'smooth', block: 'start'});
        </script>""",
        height=0,
    )
c1, c2 = st.columns([1, 1])

# Divisional (varga) charts beyond D1 are a premium feature — free accounts
# only get the plain Rāśi chart (D1) in both the diamond and wheel views.
_varga_choices_for_limit = VARGA_OPTIONS if _premium_for_limit else ["D1"]

with c1:
    st.markdown(
        '<div class="kcard"><h4 style="display:flex;justify-content:space-between;'
        'align-items:center;border-bottom:none;margin-bottom:6px;padding-bottom:0;">'
        '<span>North Indian</span></h4>',
        unsafe_allow_html=True,
    )
    diamond_varga = st.selectbox(
        "Chart", _varga_choices_for_limit, index=0, key="diamond_varga_select", label_visibility="collapsed"
    )
    st.markdown(
        f'<p class="kmuted" style="font-size:12px;margin:2px 0 10px 0;'
        f'border-bottom:2px solid {C["line"]};padding-bottom:8px;">{form["city"][0]}</p>',
        unsafe_allow_html=True,
    )
    dv_birth = make_varga_bodies(core_birth_bodies, diamond_varga)
    dv_transit = make_varga_bodies(core_transit_bodies, diamond_varga)
    dv_asc = next(b for b in dv_birth if b["key"] == "As")
    svg_diamond = build_svg_chart(
        dv_birth, dv_transit, dv_asc["sign"],
        show_nakshatra=(_premium_for_limit and _chart_show_nak),
        language=_chart_language, show_transits=_chart_show_transits,
    )
    st.components.v1.html(
        f'<div style="display:flex;justify-content:center;">{svg_diamond}</div>', height=760
    )
    if not _premium_for_limit:
        st.caption(
            "⭐ Upgrade to Premium to see each graha's Nakṣatra, and to unlock "
            "divisional charts (D2–D60)."
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
        "Chart", _varga_choices_for_limit, index=0, key="circular_varga_select", label_visibility="collapsed"
    )
    st.markdown(
        f'<p class="kmuted" style="font-size:12px;margin:2px 0 10px 0;'
        f'border-bottom:2px solid {C["line"]};padding-bottom:8px;">transits {transit_label}</p>',
        unsafe_allow_html=True,
    )
    cv_birth = make_varga_bodies(core_birth_bodies, circular_varga)
    cv_transit = make_varga_bodies(core_transit_bodies, circular_varga) if _chart_show_transits else []
    cv_asc = next(b for b in cv_birth if b["key"] == "As")
    svg_circular = build_circular_svg_chart(
        cv_birth, cv_transit, cv_asc["sign"], cv_asc["inSign"]
    )
    st.components.v1.html(
        f'<div style="display:flex;justify-content:center;">{svg_circular}</div>', height=760
    )
    if not _premium_for_limit:
        st.caption("⭐ Upgrade to Premium to unlock divisional charts (D2–D60) on the wheel too.")
    st.markdown("</div>", unsafe_allow_html=True)

# ---- Chart display options (affect both charts above) ---------------------
st.markdown('<div class="kcard">', unsafe_allow_html=True)
opt1, opt2, opt3 = st.columns(3)
with opt1:
    st.checkbox(
        "Show Nakṣatra", value=_chart_show_nak, key="chart_show_nakshatra",
        disabled=not _premium_for_limit,
        help=None if _premium_for_limit else "Premium feature — upgrade to enable.",
    )
with opt2:
    st.radio(
        "Kundali language", ["English", "Hindi"], key="chart_language",
        index=["English", "Hindi"].index(_chart_language), horizontal=True,
    )
with opt3:
    st.checkbox("Show Transits", value=_chart_show_transits, key="chart_show_transits")
st.markdown("</div>", unsafe_allow_html=True)

if _premium_for_limit:
    st.markdown('<div class="kcard">', unsafe_allow_html=True)
    _birth_dt = datetime.combine(form["dob"], form["tob"])
    render_running_dashas(birth_chart, core_birth_bodies, _birth_dt)
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
        pdf_bytes = generate_kundali_pdf_bytes(birth_chart, form, transit_chart)
        st.download_button(
            "📄 Download Kundali PDF", data=pdf_bytes,
            file_name=f"kundali_{form['city'][0]}_{form['dob'].isoformat()}.pdf",
            mime="application/pdf", use_container_width=True,
        )
    else:
        st.info("Install `fpdf2` (`pip install fpdf2`) to enable PDF export. "
                "Meanwhile, here's an HTML report you can save or print to PDF from your browser.")
        html_report = generate_kundali_html_report(birth_chart, form, transit_chart)
        st.download_button(
            "📄 Download Kundali Report (HTML)", data=html_report,
            file_name=f"kundali_{form['city'][0]}_{form['dob'].isoformat()}.html",
            mime="text/html", use_container_width=True,
        )

    st.markdown('<div style="margin-top:18px;padding:0;overflow:hidden;">', unsafe_allow_html=True)
    _birth_dt_report = datetime.combine(form["dob"], form["tob"])
    render_dasha_explorer(birth_chart, core_birth_bodies, _birth_dt_report)
    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-transit"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">🔄 Nakshatra Live &amp; Current Transits</h4>', unsafe_allow_html=True)
    st.markdown('<p style="color:{0};font-weight:700;margin-bottom:6px;">🌟 Nakshatra Live</p>'.format(C["gold"]), unsafe_allow_html=True)
    render_nakshatra_live_clock(lat, lon, tz)
    st.markdown(f'<p style="color:{C["gold"]};font-weight:700;margin-top:20px;margin-bottom:6px;">🔄 Current Transits</p>', unsafe_allow_html=True)
    st.markdown(f'<p class="kmuted" style="margin-bottom:10px;">As of {transit_label} '
                 f'({form["city"][0]})</p>', unsafe_allow_html=True)
    t_header = "<tr><th>Graha</th><th>Degree</th><th>Zodiac Sign</th><th>Nakṣatra</th></tr>"
    t_rows = []
    _jd_now_transit = transit_chart["jd"]
    for b in core_transit_bodies:
        if b["key"] == "As":
            continue
        retro = " ℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
        color = PLANET_TRANSIT_COLORS.get(b["key"], C["ivory"])
        entry_jd, exit_jd = compute_nakshatra_transit_window(b["key"], _jd_now_transit, b["nakIdx"])
        entry_str = jd_to_local_date_str(entry_jd, tz) if entry_jd else "\u2014"
        exit_str = jd_to_local_date_str(exit_jd, tz) if exit_jd else "\u2014"
        t_rows.append(
            f'<tr style="background:{color}22;">'
            f'<td class="body-key" style="color:{color};">{b["key"]}</td>'
            f'<td>{fmt_deg(b["inSign"])}{retro}</td>'
            f'<td>{SIGNS[b["sign"]]}</td>'
            f'<td>{NAKSHATRAS[b["nakIdx"]]} <span class="kmuted" style="font-size:15px;">'
            f'({entry_str} \u2013 {exit_str})</span></td></tr>'
        )
    st.markdown(
        f'<table class="gtable">{t_header}{"".join(t_rows)}</table>'
        f'<p class="kmuted" style="font-size:12px;margin-top:8px;">'
        "℞ = retrograde. Dates in brackets are when the graha entered its current nakṣatra and when it will next leave it.</p>",
        unsafe_allow_html=True,
    )

    st.markdown(f'<p style="color:{C["gold"]};font-weight:700;margin-top:18px;">Transit Insights</p>', unsafe_allow_html=True)
    _conjunctions = compute_transit_conjunctions(core_transit_bodies)
    _jd_now = transit_chart["jd"]
    _insight_cards = []
    for b in core_transit_bodies:
        if b["key"] == "As":
            continue
        retro = " ℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
        color = PLANET_TRANSIT_COLORS.get(b["key"], C["gold"])
        entry_jd, exit_jd = compute_nakshatra_transit_window(b["key"], _jd_now, b["nakIdx"])
        entry_str = jd_to_local_date_str(entry_jd, tz) if entry_jd else "before this window"
        exit_str = jd_to_local_date_str(exit_jd, tz) if exit_jd else "beyond this window"
        insight_text = build_transit_insight(b, _conjunctions.get(b["key"], []))
        _insight_cards.append(
            f'<details style="background:{C["panel"]}; '
            f'border:1px solid {C["line"]}; border-left:5px solid {color}; border-radius:10px; '
            f'margin-bottom:12px; padding:16px 20px;">'
            f'<summary style="cursor:pointer; font-weight:700; color:{color}; font-size:18px;">'
            f'{b["key"]} — {BODY_FULLNAME_ASCII.get(b["key"], b["key"])} in {SIGNS[b["sign"]]}{retro} '
            f'({NAKSHATRAS[b["nakIdx"]]})</summary>'
            f'<div style="margin-top:12px;">'
            f'<p style="font-size:17px; line-height:1.55;">{insight_text}</p>'
            f'<p style="font-size:16px;background:{C["panelSoft"]};border-radius:6px;padding:10px 14px;margin-top:10px;">'
            f'<b>In {NAKSHATRAS[b["nakIdx"]]} from</b> {entry_str} <b>to</b> {exit_str}'
            f'{" (still transiting)" if not exit_jd else ""}</p>'
            f'</div></details>'
        )
    st.markdown("".join(_insight_cards), unsafe_allow_html=True)
    st.caption(
        "⚠️ General, educational context about the current sky — not a personalised prediction. "
        "A full transit reading also weighs your natal chart (which houses these transits activate "
        "for you specifically), classical aspects (drishti) between planets, and more. Entry/exit "
        "dates are computed directly from this app's ephemeris, in the birth location's local time."
    )

    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-remedies"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">📿 Day-wise Remedies</h4>', unsafe_allow_html=True)
    today_idx = date.today().isoweekday() % 7  # 0=Sunday .. 6=Saturday
    r_header = "<tr><th>Day</th><th>Graha</th><th>Gemstone</th><th>Colour</th><th>Suggested Practice</th></tr>"
    r_rows = []
    for i, (day_name, key, gem, colour, remedy) in enumerate(DAY_REMEDIES):
        style = f' style="background:{C["panelSoft"]};font-weight:700;"' if i == today_idx else ""
        r_rows.append(
            f'<tr{style}><td>{day_name}{" (today)" if i == today_idx else ""}</td>'
            f'<td>{BODY_FULLNAME_ASCII.get(key, key)}</td><td>{gem}</td><td>{colour}</td>'
            f'<td>{remedy}</td></tr>'
        )
    st.markdown(f'<table class="gtable">{r_header}{"".join(r_rows)}</table>', unsafe_allow_html=True)
    st.caption(
        "⚠️ General traditional associations, not a personalised prescription — gemstones in "
        "particular should only be worn after a proper chart analysis, since an unsuitable one "
        "can do more harm than good for some charts."
    )

    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-navtara"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">🌙 Navtara Chakra</h4>', unsafe_allow_html=True)
    render_navtara_chakra_tab(b_moon["nakIdx"], tz)

    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-muhurta"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">🕉️ Panchang & Muhurta</h4>', unsafe_allow_html=True)
    pm_mode = st.radio(
        "Mode", ["Daily Panchang", "Find Muhurta", "Hora Timings"], horizontal=True, key="pm_mode",
        label_visibility="collapsed",
    )

    if pm_mode == "Daily Panchang":
        pm_date = st.date_input("Date", value=date.today(), key="pm_panchang_date")
        pmw = compute_muhurta_windows(pm_date.year, pm_date.month, pm_date.day, lat, lon, tz)
        pm_chart = compute_chart(pm_date.year, pm_date.month, pm_date.day, 12, 0, lat, lon, tz)
        pm_pan = pm_chart["panchanga"]
        st.markdown(
            f"""
            <div class="kcard" style="margin-top:10px;">
              <div class="krow"><span class="kmuted">Vāra</span><span>{VARAS[pm_date.isoweekday() % 7]}</span></div>
              <div class="krow"><span class="kmuted">Tithi</span><span>{pm_pan['paksha']} {pm_pan['tithiName']}</span></div>
              <div class="krow"><span class="kmuted">Nakṣatra</span><span>{NAKSHATRAS[pm_pan['nakIdx']]}</span></div>
              <div class="krow"><span class="kmuted">Yoga</span><span>{YOGAS[pm_pan['yogaIdx']]}</span></div>
              <div class="krow"><span class="kmuted">Karaṇa</span><span>{pm_pan['karana']}</span></div>
              <div class="krow"><span class="kmuted">Sunrise</span><span>{_fmt_hm(pmw['sunrise'])}</span></div>
              <div class="krow"><span class="kmuted">Sunset</span><span>{_fmt_hm(pmw['sunset'])}</span></div>
              <div class="krow"><span class="ksindoor">Abhijit Muhūrta</span><span class="ksindoor">{_fmt_hm(pmw['abhijit'][0])} – {_fmt_hm(pmw['abhijit'][1])}</span></div>
              <div class="krow"><span class="kmuted">Rāhu Kālam (avoid)</span><span>{_fmt_hm(pmw['rahu_kalam'][0])} – {_fmt_hm(pmw['rahu_kalam'][1])}</span></div>
              <div class="krow"><span class="kmuted">Yamaganda (avoid)</span><span>{_fmt_hm(pmw['yamaganda'][0])} – {_fmt_hm(pmw['yamaganda'][1])}</span></div>
              <div class="krow"><span class="kmuted">Gulika Kālam (avoid)</span><span>{_fmt_hm(pmw['gulika_kalam'][0])} – {_fmt_hm(pmw['gulika_kalam'][1])}</span></div>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.caption(f"Calculated for {form['city'][0]} ({form['city'][1]}).")

    elif pm_mode == "Find Muhurta":
        st.markdown('<p class="kmuted" style="margin-bottom:6px;">What are you planning?</p>', unsafe_allow_html=True)
        activity = st.selectbox(
            "Activity", list(MUHURTA_ACTIVITIES.keys()), key="muhurta_activity",
            label_visibility="collapsed",
        )
        mcol1, mcol2 = st.columns(2)
        with mcol1:
            search_from = st.date_input("Search from", value=date.today(), key="muhurta_from")
        with mcol2:
            range_days = st.number_input(
                "Range (days)", min_value=7, max_value=180, value=45, step=1, key="muhurta_range"
            )
        exclude_overlap = st.checkbox(
            "Exclude Rāhu, Gulika and Yamaganda overlap with Abhijit", value=True, key="muhurta_exclude"
        )
        if st.button("🔍 Find calculated windows", use_container_width=True, key="muhurta_search"):
            found = find_muhurta_windows(
                activity, search_from, int(range_days), lat, lon, tz,
                exclude_kalam_overlap=exclude_overlap,
            )
            st.session_state["muhurta_results"] = found

        results = st.session_state.get("muhurta_results")
        if results is not None:
            if not results:
                st.warning("No windows scored 50% or higher in this range — try widening the range or picking a different activity.")
            else:
                st.markdown(
                    f'<p class="ksindoor" style="font-weight:700;margin:14px 0 10px;">'
                    f'{len(results)} Panchāṅga-screened window(s) found</p>',
                    unsafe_allow_html=True,
                )
                for i, r in enumerate(results, 1):
                    pct = int(round(r["score"] * 100))
                    d = r["date"]
                    st.markdown(
                        f"""
                        <div class="kcard" style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;">
                          <div>
                            <p class="kmuted" style="font-size:12px;margin:0 0 2px;">
                              {d.strftime('%A, %d %B %Y')} &middot; {NAKSHATRAS[r['nak_idx']]}</p>
                            <p style="font-size:20px;font-weight:700;margin:0 0 4px;">
                              {_fmt_hm(r['abhijit'][0])} – {_fmt_hm(r['abhijit'][1])}</p>
                            <p class="kmuted" style="font-size:13px;margin:0;">
                              {r['paksha']} {r['tithi_name']} &middot; {YOGAS[r['yoga_idx']]} &middot;
                              screened outside Rāhu, Gulika and Yamaganda</p>
                          </div>
                          <div style="text-align:center;flex-shrink:0;margin-left:16px;">
                            <div style="width:56px;height:56px;border-radius:50%;background:{C['panelSoft']};
                              border:2px solid {C['gold']};display:flex;align-items:center;justify-content:center;
                              font-size:20px;color:{C['gold']};">&#10003;</div>
                            <p class="kmuted" style="font-size:11px;margin:4px 0 0;">{pct}% rules</p>
                          </div>
                        </div>
                        """,
                        unsafe_allow_html=True,
                    )
        st.caption(
            "⚠️ General traditional guidance (favourable weekday, nakṣatra, and avoiding rikta tithi / "
            "Rāhu-Gulika-Yamaganda overlap for the midday Abhijit window) — not a substitute for a full "
            "professional muhūrta consultation, which also weighs the lagna at the exact moment, planetary "
            "strength, and doṣas beyond what's checked here."
        )

    else:
        hcol_date, hcol_place = st.columns([1, 1.5])
        with hcol_date:
            hora_date = st.date_input("Date", value=date.today(), key="hora_date")
        with hcol_place:
            hora_city_query = st.text_input(
                "Location", value=form["city"][0], key="hora_city_query",
                help="Hora timings depend on sunrise/sunset, which vary by place.",
            )
            hora_matches = [c for c in CITIES if hora_city_query.lower() in (c[0] + " " + c[1]).lower()]
            if not hora_matches:
                hora_matches = CITIES[:8]
            hora_labels = [f"{c[0]} \u00b7 {c[1]}" for c in hora_matches[:8]]
            hora_chosen_label = st.selectbox("Match", hora_labels, key="hora_city_sel", label_visibility="collapsed")
            hora_city = hora_matches[hora_labels.index(hora_chosen_label)]
        hora_lat, hora_lon, hora_tz = hora_city[2], hora_city[3], hora_city[4]
        st.caption(
            f"{abs(hora_lat):.2f}\u00b0{'N' if hora_lat >= 0 else 'S'}, "
            f"{abs(hora_lon):.2f}\u00b0{'E' if hora_lon >= 0 else 'W'} \u00b7 "
            f"UTC{'+' if hora_tz >= 0 else ''}{hora_tz}"
        )
        hora = compute_hora_table(hora_date.year, hora_date.month, hora_date.day, hora_lat, hora_lon, hora_tz)
        EFF_COLOR = {
            "Most-effective": "#1E8E3E", "Detrimental": "#C4462B",
            "Less-effective": "#1A73E8", "Neutral": C["ivory"],
        }

        def _hora_rows(horas):
            rows = []
            for h in horas:
                color = EFF_COLOR[h["effectiveness"]]
                star = " *" if h["next_day"] else ""
                rows.append(
                    f'<tr><td style="color:{color};font-weight:600;">{BODY_FULLNAME_ASCII.get(h["lord"], h["lord"])}</td>'
                    f'<td>{_fmt_hm(h["start"])} \u2013 {_fmt_hm(h["end"])}{star}</td></tr>'
                )
            return "".join(rows)

        hcol1, hcol2 = st.columns(2)
        with hcol1:
            st.markdown(
                f'<table class="gtable"><tr><th colspan="2" style="text-align:center;">Day Hora</th></tr>'
                f'<tr><th>Hora</th><th>Time</th></tr>{_hora_rows(hora["day"])}</table>',
                unsafe_allow_html=True,
            )
        with hcol2:
            st.markdown(
                f'<table class="gtable"><tr><th colspan="2" style="text-align:center;">Night Hora</th></tr>'
                f'<tr><th>Hora</th><th>Time</th></tr>{_hora_rows(hora["night"])}</table>',
                unsafe_allow_html=True,
            )
        st.markdown(
            f'<div style="display:flex;gap:18px;flex-wrap:wrap;font-size:13px;margin-top:12px;">'
            f'<span style="color:{EFF_COLOR["Most-effective"]};font-weight:600;">\u25a0 Most-effective</span>'
            f'<span style="color:{EFF_COLOR["Detrimental"]};font-weight:600;">\u25a0 Detrimental</span>'
            f'<span style="color:{EFF_COLOR["Less-effective"]};font-weight:600;">\u25a0 Less-effective</span>'
            f'<span class="kmuted">* = next calendar day</span></div>',
            unsafe_allow_html=True,
        )
        st.caption(
            "⚠️ Each hora divides sunrise-to-sunset (and that sunset to the next sunrise) into 12 equal "
            "parts, ruled by the 7 classical grahas in continuous Chaldean order (Saturn, Jupiter, Mars, "
            "Sun, Venus, Mercury, Moon). General timing guidance — a full electional analysis also weighs "
            "tithi, nakṣatra, and the lagna at that moment."
        )

    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-compat"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">💞 Compatibility</h4>', unsafe_allow_html=True)
    st.markdown(
        '<p class="kmuted" style="margin-bottom:14px;">Checks Moon (nakṣatra tara + sign-lord friendship), '
        'Ascendant (lord friendship + house relationship), and Jupiter (dignity + cross-placement to the '
        'partner\'s Moon) between two birth charts.</p>',
        unsafe_allow_html=True,
    )
    cp_a, cp_b = st.columns(2)
    with cp_a:
        st.markdown(f'<p style="color:{C["gold"]};font-weight:700;">PERSON A</p>', unsafe_allow_html=True)
        a_name = st.text_input("Name", value="Person A", key="compat_a_name")
        a_dob = st.date_input("Date of birth", value=date(1995, 6, 12), key="compat_a_dob",
                               min_value=date(1900, 1, 1), max_value=date(2100, 12, 31))
        a_h, a_m = st.columns(2)
        with a_h:
            a_hour = st.number_input("Hour", min_value=0, max_value=23, value=10, key="compat_a_hour")
        with a_m:
            a_min = st.number_input("Minute", min_value=0, max_value=59, value=30, key="compat_a_min")
        a_city_query = st.text_input("Birth place", value="Bathinda", key="compat_a_city")
        a_matches = [c for c in CITIES if a_city_query.lower() in (c[0] + " " + c[1]).lower()] or CITIES[:5]
        a_city_label = st.selectbox("Match", [f"{c[0]} · {c[1]}" for c in a_matches[:5]], key="compat_a_city_sel")
        a_city = a_matches[[f"{c[0]} · {c[1]}" for c in a_matches[:5]].index(a_city_label)]

    with cp_b:
        st.markdown(f'<p style="color:{C["sindoor"]};font-weight:700;">PERSON B</p>', unsafe_allow_html=True)
        b_name = st.text_input("Name", value="Person B", key="compat_b_name")
        b_dob = st.date_input("Date of birth", value=date(1994, 3, 20), key="compat_b_dob",
                               min_value=date(1900, 1, 1), max_value=date(2100, 12, 31))
        b_h, b_m = st.columns(2)
        with b_h:
            b_hour = st.number_input("Hour", min_value=0, max_value=23, value=14, key="compat_b_hour")
        with b_m:
            b_min = st.number_input("Minute", min_value=0, max_value=59, value=15, key="compat_b_min")
        b_city_query = st.text_input("Birth place", value="Bathinda", key="compat_b_city")
        b_matches = [c for c in CITIES if b_city_query.lower() in (c[0] + " " + c[1]).lower()] or CITIES[:5]
        b_city_label = st.selectbox("Match", [f"{c[0]} · {c[1]}" for c in b_matches[:5]], key="compat_b_city_sel")
        b_city = b_matches[[f"{c[0]} · {c[1]}" for c in b_matches[:5]].index(b_city_label)]

    if st.button("💞 Calculate compatibility", use_container_width=True, key="compat_calc_btn"):
        chart_a = compute_chart(a_dob.year, a_dob.month, a_dob.day, int(a_hour), int(a_min),
                                 a_city[2], a_city[3], a_city[4])
        chart_b = compute_chart(b_dob.year, b_dob.month, b_dob.day, int(b_hour), int(b_min),
                                 b_city[2], b_city[3], b_city[4])
        st.session_state["compat_result"] = compute_compatibility(chart_a, chart_b)
        st.session_state["compat_names"] = (a_name or "Person A", b_name or "Person B")

    result = st.session_state.get("compat_result")
    if result:
        n_a, n_b = st.session_state.get("compat_names", ("Person A", "Person B"))
        st.markdown(
            f"""
            <div class="kcard" style="text-align:center;margin-top:16px;border:2px solid {C['gold']};">
              <p style="font-size:15px;color:{C['muted']};margin:0;">{n_a} &#10084; {n_b}</p>
              <p style="font-size:42px;font-weight:700;color:{C['gold']};margin:6px 0;">
                {result['total']:.1f} <span style="font-size:20px;color:{C['muted']};">/ {result['max_total']:.0f}</span></p>
              <p style="font-size:16px;font-weight:700;color:{C['sindoor']};margin:0;">{result['verdict']}</p>
              <p class="kmuted" style="font-size:13px;margin-top:4px;">{result['pct']:.0f}% overall</p>
            </div>
            """,
            unsafe_allow_html=True,
        )
        rows_html = "".join(
            f'<tr><td>{label}</td><td>{detail}</td>'
            f'<td style="text-align:right;font-weight:700;">{score:.2f} / {maxs:.0f}</td></tr>'
            for label, score, maxs, detail in result["components"]
        )
        st.markdown(
            f'<table class="gtable" style="margin-top:14px;">'
            f'<tr><th>Factor</th><th>Detail</th><th style="text-align:right;">Score</th></tr>'
            f'{rows_html}</table>',
            unsafe_allow_html=True,
        )
        st.caption(
            "⚠️ This checks a focused subset — Moon, Ascendant, and Jupiter only — not the full classical "
            "Aṣṭakoota Guṇa Milan (which scores eight factors — Varna, Vashya, Tara, Yoni, Graha Maitri, "
            "Gaṇa, Bhakoot, Nāḍī — out of 36). Treat this as a partial, general indicator, not a complete "
            "traditional match report; a full consultation weighs considerably more than what's checked here."
        )
    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-charts"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">📁 Charts</h4>', unsafe_allow_html=True)
    st.markdown(
        '<p class="kmuted" style="margin-bottom:10px;">Save the chart currently shown above, and reload any '
        'previously saved chart — handy for family members or repeat clients.</p>',
        unsafe_allow_html=True,
    )
    sc_col1, sc_col2 = st.columns([2, 1])
    with sc_col1:
        chart_label = st.text_input(
            "Label for this chart", value=(form.get("name") or "Untitled chart"), key="save_chart_label",
        )
    with sc_col2:
        st.markdown("<br>", unsafe_allow_html=True)
        if st.button("💾 Save this chart", use_container_width=True, key="save_chart_btn"):
            save_chart_to_library(
                user_id, chart_label.strip() or "Untitled chart", form.get("name", ""),
                form["dob"].isoformat(), form["tob"].isoformat(),
                form["city"][0], form["city"][1], form["city"][2], form["city"][3], form["city"][4],
            )
            st.success(f"Saved “{chart_label.strip() or 'Untitled chart'}” to your chart library.")

    saved = list_saved_charts(user_id)
    if not saved:
        st.caption("No saved charts yet — cast a chart above, then save it here.")
    else:
        st.markdown(f'<p class="kmuted" style="margin-top:14px;">{len(saved)} saved chart(s)</p>', unsafe_allow_html=True)
        for sc in saved:
            sc_dob = date.fromisoformat(sc["dob"])
            sc_tob = dtime.fromisoformat(sc["tob"])
            row_l, row_load, row_del = st.columns([4, 1, 1])
            with row_l:
                st.markdown(
                    f'<div class="krow" style="border-bottom:none;">'
                    f'<span><b>{sc["label"]}</b> — {sc["name"] or "unnamed"}</span>'
                    f'<span class="kmuted">{sc_dob.strftime("%d %b %Y")} · {sc_tob.strftime("%H:%M")} · '
                    f'{sc["city_name"]}</span></div>',
                    unsafe_allow_html=True,
                )
            with row_load:
                if st.button("Load", key=f"load_chart_{sc['id']}", use_container_width=True):
                    st.session_state["_load_chart_override"] = {
                        "label": sc["label"], "name": sc["name"] or "", "gender": sc["gender"] if "gender" in sc.keys() else None,
                        "dob": sc_dob, "tob": sc_tob,
                        "city": (sc["city_name"], sc["city_region"], sc["lat"], sc["lon"], sc["tz"]),
                    }
                    st.rerun()
            with row_del:
                if st.button("Delete", key=f"delete_chart_{sc['id']}", use_container_width=True):
                    delete_saved_chart(sc["id"], user_id)
                    st.rerun()
    st.markdown("</div>", unsafe_allow_html=True)

    st.markdown('<div id="section-numerology"></div>', unsafe_allow_html=True)
    st.markdown(f'<div class="kcard" style="border-top:3px solid {C["gold"]};"><h4 style="margin-bottom:14px;">🔢 Numerology</h4>', unsafe_allow_html=True)

    with st.expander("What's the difference between Pythagorean and Chaldean numerology?", expanded=False):
        st.markdown(
            "**Pythagorean** (the more common Western system) assigns letters to numbers 1–9 strictly "
            "in alphabetical order (A=1, B=2, C=3 ... I=9, then repeating J=1, K=2...), works from your "
            "**birth name** as legally recorded, and treats **11, 22, and 33** as special 'master numbers' "
            "that are never reduced further.\n\n"
            "**Chaldean** (the older system, with roots in ancient Babylon) assigns letters to numbers "
            "based on **sound/vibration** rather than alphabetical order — notably, no letter is ever "
            "assigned the number **9**, since it's considered sacred and reserved for outcomes, not inputs. "
            "Chaldean traditionally favors the **name you currently go by** (not necessarily your birth "
            "name), reduces every number fully to a single digit (no master numbers), and additionally "
            "weighs the *unreduced* 'compound number' of a name for extra meaning.\n\n"
            "Because the letter-value tables and reduction rules differ, **the two systems will usually "
            "give different numbers for the same name** — this isn't an error, they're simply different "
            "traditions. This page keeps every calculation strictly within its own system."
        )

    with st.form("numerology_form"):
        nc1, nc2 = st.columns(2)
        with nc1:
            num_full_name = st.text_input("Full Name (as on birth record)", key="num_full_name")
            num_dob = st.date_input("Date of Birth", value=date(1995, 1, 1), min_value=date(1900, 1, 1),
                                     max_value=date(2100, 12, 31), key="num_dob")
            num_preferred_name = st.text_input("Preferred / current name (optional)", key="num_preferred_name",
                                                help="Chaldean numerology traditionally uses the name you currently go by.")
        with nc2:
            num_gender = st.selectbox("Gender (optional)", ["Prefer not to say", "Female", "Male", "Other"], key="num_gender")
            num_birth_place = st.text_input("Birth location (optional)", key="num_birth_place")
            num_email = st.text_input("Email (optional, for saving this report)", key="num_email")
        num_submit = st.form_submit_button("Generate Numerology Profile", use_container_width=True)

    if num_submit:
        if not num_full_name.strip():
            st.error("Enter your full name to generate a profile.")
        elif not _clean_name(num_full_name):
            st.error(
                "Both Pythagorean and Chaldean numerology, as implemented here, are defined over the "
                "Latin alphabet (A-Z) — enter your name using Latin letters (a romanized spelling works "
                "fine) so the letter-to-number tables can be applied."
            )
        else:
            st.session_state["numerology_result"] = {
                "full_name": num_full_name.strip(),
                "preferred_name": num_preferred_name.strip(),
                "dob": num_dob.isoformat(),
                "gender": num_gender,
                "birth_place": num_birth_place.strip(),
                "email": num_email.strip(),
            }
            if num_email.strip():
                st.info("📧 Email capture noted — this app doesn't currently have email-sending "
                        "infrastructure set up, so no report is actually emailed yet. Your results "
                        "are shown below and can be saved to your Charts library instead.")

    result = st.session_state.get("numerology_result")
    if result:
        r_dob = date.fromisoformat(result["dob"])
        name_for_expression = result["preferred_name"] or result["full_name"]

        py_life_path = pythagorean_life_path(r_dob)
        py_expression = pythagorean_expression(result["full_name"])
        py_soul_urge = pythagorean_soul_urge(result["full_name"])
        py_personality = pythagorean_personality(result["full_name"])
        py_birthday = pythagorean_birthday_number(r_dob)
        py_maturity = pythagorean_maturity(py_life_path, py_expression)
        py_personal_year = pythagorean_personal_year(r_dob, date.today().year)
        py_attitude = pythagorean_attitude(r_dob)
        py_balance = pythagorean_balance(result["full_name"])
        py_hidden_passion = pythagorean_hidden_passion(result["full_name"])
        py_karmic_lessons = pythagorean_karmic_lessons(result["full_name"])
        py_subconscious = pythagorean_subconscious_self(result["full_name"])
        _, py_life_path_debt = _reduce_with_karmic_debt(
            reduce_number(r_dob.month, True) + reduce_number(r_dob.day, True) + reduce_number(r_dob.year, True),
            preserve_master=True,
        )

        ch_life = chaldean_life_number(r_dob)
        ch_name = chaldean_name_number(name_for_expression)

        st.markdown(f'<p style="font-family:Georgia,serif;font-size:20px;color:{C["ivory"]};margin-top:10px;">'
                    f'Numerology Profile — {result["full_name"]}</p>', unsafe_allow_html=True)

        pcol, ccol = st.columns(2)
        with pcol:
            st.markdown(f'<div class="kcard" style="border:2px solid {C["gold"]};">'
                        f'<h4 style="font-size:15px;">Pythagorean System</h4>', unsafe_allow_html=True)
            py_rows = [
                ("Life Path Number", py_life_path, "From your date of birth — your core life theme."),
                ("Expression (Destiny) Number", py_expression, "From all letters of your birth name — your natural talents."),
                ("Soul Urge (Heart's Desire)", py_soul_urge, "From the vowels in your name — your inner motivation."),
                ("Personality Number", py_personality, "From the consonants in your name — how others perceive you."),
                ("Birthday Number", py_birthday, "The day of the month you were born, reduced."),
                ("Maturity Number", py_maturity, "Life Path + Expression — the theme of your later years."),
                (f"Personal Year ({date.today().year})", py_personal_year, "The theme of your current calendar year."),
                ("Attitude Number", py_attitude, "Birth month + birth day — your first reaction to situations."),
                ("Balance Number", py_balance if py_balance else "—", "From the initials of each name part — how you regain composure under stress."),
                ("Hidden Passion Number", py_hidden_passion if py_hidden_passion else "—", "The number appearing most often in your name — a standout natural talent."),
                ("Subconscious Self Number", py_subconscious, "9 minus your karmic lessons — resourcefulness in a crisis, by this tradition."),
            ]
            for label, val, desc in py_rows:
                meaning = NUMEROLOGY_MEANINGS_PYTHAGOREAN.get(val, "") if isinstance(val, int) else ""
                st.markdown(
                    f'<div class="krow"><span class="kmuted">{label}</span>'
                    f'<span class="ksindoor" style="font-weight:700;font-size:18px;">{val}</span></div>'
                    f'<p class="kmuted" style="font-size:12px;margin:-2px 0 8px;">{desc} {meaning}</p>',
                    unsafe_allow_html=True,
                )
            karmic_text = (
                ", ".join(str(n) for n in py_karmic_lessons) if py_karmic_lessons
                else "none — every number 1-9 appears somewhere in your name"
            )
            st.markdown(
                f'<div class="krow"><span class="kmuted">Karmic Lessons (missing numbers)</span>'
                f'<span class="ksindoor" style="font-weight:700;font-size:16px;">{karmic_text}</span></div>'
                f'<p class="kmuted" style="font-size:12px;margin:-2px 0 8px;">Numbers absent from your name\'s '
                f'letters — traditionally read as themes life keeps presenting lessons in, not scientific fact.</p>',
                unsafe_allow_html=True,
            )
            if py_life_path_debt:
                st.markdown(
                    f'<div style="background:{C["panelSoft"]};border-radius:8px;padding:8px 12px;margin-top:6px;">'
                    f'<b>Karmic Debt {py_life_path_debt}/{py_life_path}</b> appeared while calculating your Life '
                    f'Path. {KARMIC_DEBT_MEANINGS.get(py_life_path_debt, "")}</div>',
                    unsafe_allow_html=True,
                )
            st.markdown("</div>", unsafe_allow_html=True)

        with ccol:
            st.markdown(f'<div class="kcard" style="border:2px solid {C["sindoor"]};">'
                        f'<h4 style="font-size:15px;">Chaldean System</h4>', unsafe_allow_html=True)
            st.markdown(
                f'<div class="krow"><span class="kmuted">Life / Birth Number</span>'
                f'<span class="ksindoor" style="font-weight:700;font-size:18px;">{ch_life}</span></div>'
                f'<p class="kmuted" style="font-size:12px;margin:-2px 0 8px;">From every digit of your full '
                f'date of birth, fully reduced. {NUMEROLOGY_MEANINGS_CHALDEAN.get(ch_life, "")}</p>',
                unsafe_allow_html=True,
            )
            name_label = "Preferred name" if result["preferred_name"] else "Full name"
            st.markdown(
                f'<div class="krow"><span class="kmuted">Name Number ({name_label})</span>'
                f'<span class="ksindoor" style="font-weight:700;font-size:18px;">{ch_name["reduced"]} '
                f'<span class="kmuted" style="font-size:13px;">(compound {ch_name["compound"]})</span></span></div>'
                f'<p class="kmuted" style="font-size:12px;margin:-2px 0 8px;">From {name_label.lower()}, using '
                f'Chaldean sound-based letter values. {NUMEROLOGY_MEANINGS_CHALDEAN.get(ch_name["reduced"], "")}</p>',
                unsafe_allow_html=True,
            )
            harmony = "harmonious" if ch_life == ch_name["reduced"] else "worth reflecting on together"
            st.markdown(
                f'<p style="font-size:13px;margin-top:10px;">Your Life Number ({ch_life}) and Name Number '
                f'({ch_name["reduced"]}) are <b>{harmony}</b> in this reading.</p>',
                unsafe_allow_html=True,
            )
            st.markdown("</div>", unsafe_allow_html=True)

        st.caption(
            "⚠️ Numerology is a symbolic/traditional system, not an empirically validated one — treat this "
            "as a reflective tool rather than a factual claim about your personality or future. The two "
            "systems above are computed independently using their own letter tables and rules; a differing "
            "result between them doesn't mean either is 'wrong'."
        )

        st.markdown(f'<p style="font-family:Georgia,serif;font-size:18px;color:{C["ivory"]};margin-top:22px;">'
                    f'🔲 Lo Shu Grid</p>', unsafe_allow_html=True)
        loshu = compute_lo_shu_grid(r_dob)
        grid_rows_html = []
        for row in [[4, 9, 2], [3, 5, 7], [8, 1, 6]]:
            cells = []
            for n in row:
                c = loshu["counts"][n]
                shown = str(n) * c if c else ""
                bg = C["panelSoft"] if c else "#fff"
                cells.append(
                    f'<td style="border:1px solid {C["line"]};width:70px;height:70px;text-align:center;'
                    f'background:{bg};font-size:{18 if c<=2 else 14}px;font-weight:700;color:{C["ivory"] if c else C["muted"]};">'
                    f'{shown if shown else "·"}</td>'
                )
            grid_rows_html.append("<tr>" + "".join(cells) + "</tr>")
        lcol1, lcol2 = st.columns([1, 1.4])
        with lcol1:
            st.markdown(
                f'<table style="border-collapse:collapse;margin:0 auto;">{"".join(grid_rows_html)}</table>',
                unsafe_allow_html=True,
            )
        with lcol2:
            st.markdown(
                f'<p style="font-size:13px;"><b>Missing numbers:</b> {", ".join(map(str, loshu["missing"])) or "none"}</p>'
                f'<p style="font-size:13px;"><b>Repeated numbers:</b> {", ".join(map(str, loshu["repeated"])) or "none"}</p>'
                f'<p style="font-size:13px;"><b>Arrows present:</b> {", ".join(loshu["arrows_present"]) or "none"}</p>'
                f'<p style="font-size:13px;"><b>Arrows missing:</b> {", ".join(loshu["arrows_missing"]) or "none"}</p>',
                unsafe_allow_html=True,
            )
        st.caption(
            "⚠️ The Lo Shu Grid is a Chinese numerological tradition — 'arrows' are lines of three cells "
            "that are either all filled (a traditional strength) or all empty (a traditional growth area). "
            "This is an interpretive framework, not a diagnostic tool."
        )

    st.markdown('<p style="font-family:Georgia,serif;font-size:18px;color:{0};margin-top:26px;">'
                '✨ Master Numbers 11, 22, 33</p>'.format(C["ivory"]), unsafe_allow_html=True)
    with st.expander("When are 11, 22, and 33 treated as Master Numbers?"):
        st.markdown(
            "In Pythagorean numerology, whenever a calculation's running total lands on **11, 22, or 33**, "
            "it is traditionally left as-is rather than reduced further (so 11 is not treated as a 2, 22 is "
            "not treated as a 4, and 33 is not treated as a 6) — this app follows that convention throughout "
            "its Pythagorean calculations. Chaldean numerology, by contrast, does not use master numbers at "
            "all; every Chaldean result above is fully reduced to a single digit.\n\n"
            "- **11** — intuition and inspiration amplified; a heightened 2, often described as bringing "
            "spiritual insight alongside emotional sensitivity that needs conscious grounding.\n"
            "- **22** — the 'master builder'; a heightened 4, traditionally associated with turning big "
            "visions into real, lasting structures.\n"
            "- **33** — the 'master teacher'; a heightened 6, traditionally associated with large-scale, "
            "selfless service and compassion.\n\n"
            "Master numbers are traditionally described as carrying more intensity and higher potential, "
            "but also more inner tension, than their reduced counterpart — this is a traditional "
            "interpretation, not a measurable claim."
        )

    st.markdown('<p style="font-family:Georgia,serif;font-size:18px;color:{0};margin-top:22px;">'
                '💞 Numerology Compatibility</p>'.format(C["ivory"]), unsafe_allow_html=True)
    with st.form("numerology_compat_form"):
        nca, ncb = st.columns(2)
        with nca:
            st.markdown("**Person A**")
            compat_name_a = st.text_input("Full name", key="compat_num_name_a")
            compat_dob_a = st.date_input("Date of birth", value=date(1995, 1, 1),
                                          min_value=date(1900, 1, 1), max_value=date(2100, 12, 31), key="compat_num_dob_a")
        with ncb:
            st.markdown("**Person B**")
            compat_name_b = st.text_input("Full name", key="compat_num_name_b")
            compat_dob_b = st.date_input("Date of birth", value=date(1995, 1, 1),
                                          min_value=date(1900, 1, 1), max_value=date(2100, 12, 31), key="compat_num_dob_b")
        compat_submit = st.form_submit_button("Calculate Compatibility", use_container_width=True)

    if compat_submit:
        if not compat_name_a.strip() or not compat_name_b.strip():
            st.error("Enter both names to calculate compatibility.")
        elif not _clean_name(compat_name_a) or not _clean_name(compat_name_b):
            st.error("Both names need to be entered using Latin letters (A-Z) for this calculation.")
        else:
            st.session_state["numerology_compat_result"] = compute_numerology_compatibility(
                compat_name_a.strip(), compat_dob_a, compat_name_b.strip(), compat_dob_b
            )

    compat_result = st.session_state.get("numerology_compat_result")
    if compat_result:
        st.markdown(
            f'<div class="kcard" style="text-align:center;border:2px solid {C["gold"]};">'
            f'<p style="font-size:38px;font-weight:700;color:{C["gold"]};margin:6px 0;">'
            f'{compat_result["overall"]}<span style="font-size:18px;color:{C["muted"]};">/100</span></p>'
            f'<p style="font-size:16px;font-weight:700;color:{C["sindoor"]};margin:0;">{compat_result["band"]}</p>'
            f'</div>',
            unsafe_allow_html=True,
        )
        cat_html = "".join(
            f'<div class="krow"><span class="kmuted">{cat}</span>'
            f'<span style="font-weight:700;">{score}/100</span></div>'
            for cat, score in compat_result["categories"].items()
        )
        st.markdown(f'<div class="kcard">{cat_html}</div>', unsafe_allow_html=True)
        st.caption(
            "⚠️ This compatibility score is an interpretive scoring system created by this application "
            "(weighting Life Path, Expression, Soul Urge, Personality, and Birthday Number, all computed "
            "in the Pythagorean system), not a scientifically validated measurement of relationship "
            "outcomes."
        )

    st.markdown("</div>", unsafe_allow_html=True)

else:
    st.markdown(
        '<h4>⭐ Go Premium — Get Your Kundali Report</h4>'
        '<p class="kmuted">Unlock a downloadable Kundali report (birth details, graha positions, '
        'and Viṁśottarī daśā timeline) for a one-time payment.</p>',
        unsafe_allow_html=True,
    )
    if not PAYMENT_TEST_MODE and RAZORPAY_TEST_KEY:
        st.info(
            "🧪 Razorpay **Test Mode** keys are active — the real Razorpay checkout will open, "
            "but it wants Razorpay's own dummy test credentials, not a real card:\n\n"
            "- **Card:** `4111 1111 1111 1111` · any future expiry date · any CVV · "
            "then enter any 4-10 digit OTP to succeed (fewer than 4 digits simulates a decline)\n"
            "- **UPI:** enter `success@razorpay` to simulate success, or `failure@razorpay` "
            "to simulate a decline\n\n"
            "No real money moves with these — they only work because the key starts with `rzp_test_`."
        )
    pcol1, pcol2 = st.columns([1, 1])
    with pcol1:
        st.markdown(
            f'<p style="font-size:28px;font-weight:700;color:{C["gold"]};margin-bottom:0;">₹{PREMIUM_PRICE_INR}</p>'
            f'<p class="kmuted" style="margin-top:0;">one-time · lifetime access to report downloads</p>',
            unsafe_allow_html=True,
        )
    with pcol2:
        st.markdown("<br>", unsafe_allow_html=True)
        if PAYMENT_TEST_MODE:
            # ---- Test-mode path: no Razorpay call, no checkout modal, no real
            # money. Same downstream effect (premium unlocked) so you can test
            # the entire report-download flow right now.
            if st.button("🧪 Simulate Payment (Test Mode)", use_container_width=True, key="simulate_payment"):
                ok = simulate_test_payment(user_id, PREMIUM_PRICE_PAISE)
                if ok:
                    st.session_state["just_upgraded"] = True
                    st.rerun()
                else:
                    st.error("Simulated payment could not be recorded — please try again.")
        elif not st.session_state.get("premium_link_url"):
            if st.button("Get payment link", use_container_width=True, key="start_checkout"):
                try:
                    link = razorpay_create_payment_link(
                        PREMIUM_PRICE_PAISE, user_id, "Premium Kundali report",
                        user_name=form.get("name", ""),
                    )
                    record_order(user_id, link["id"], PREMIUM_PRICE_PAISE)
                    st.session_state["premium_link_url"] = link["short_url"]
                    st.session_state["premium_link_id"] = link["id"]
                    st.rerun()
                except requests.HTTPError as e:
                    st.error(f"Couldn't create a payment link — Razorpay rejected the request: {e}")
                except requests.RequestException as e:
                    st.error(f"Couldn't reach Razorpay — check your connection and try again. ({e})")

    # A real Razorpay-hosted page — opens in a new tab via a plain link, no
    # iframe embedding at all. This is what replaced the old Checkout.js-in-an-
    # iframe approach, which kept clipping/rendering broken inside a small frame.
    if not PAYMENT_TEST_MODE and st.session_state.get("premium_link_url"):
        lcol1, lcol2 = st.columns([1, 1])
        with lcol1:
            st.link_button(
                "💳 Pay ₹299 with Razorpay", st.session_state["premium_link_url"],
                use_container_width=True,
            )
        with lcol2:
            if st.button("Cancel / start over", use_container_width=True, key="cancel_checkout"):
                st.session_state.pop("premium_link_url", None)
                st.session_state.pop("premium_link_id", None)
                st.rerun()
        st.caption("Opens Razorpay's secure payment page in a new tab. Complete payment there, "
                   "then come back to this tab — you'll be upgraded automatically within a few seconds.")

    if PAYMENT_TEST_MODE:
        st.caption("🧪 Test mode active — clicking the button above instantly unlocks premium. "
                   "No Razorpay, no card, no charge.")
    else:
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
    '<tr><th class="uh">Body</th><th class="uh">Kāraka</th><th>Kāraka Meaning</th>'
    '<th class="uh">Nakṣatra</th><th>Pada</th></tr>'
)
body_rows = []
for b in birth_chart["bodies"]:
    retro_mark = " ℞" if (b["retro"] and b["key"] not in ("Ra", "Ke")) else ""
    combust_mark = " 🔥" if b.get("combust") else ""
    # the two senior Chara Kārakas (Ātmakāraka, Amātyakāraka) get the ↑ marker
    top_karaka_mark = '<span class="kmuted" style="font-size:11px;">↑</span> ' if b.get("karaka") in ("AK", "AmK") else ""
    karaka_meaning = KARAKA_MEANINGS.get(b.get("karaka"), "—")
    nak_lord = DASHA_LORD_SHORT[b["nakIdx"] % 9]
    nak_str = f'{NAKSHATRAS[b["nakIdx"]]}<span class="kmuted">({b["nakIdx"]+1})</span> <span class="lord">{nak_lord}</span>'
    body_rows.append(
        f'<tr><td><span class="body-key">{b["key"]}</span>&nbsp;'
        f'{top_karaka_mark}{b["name"]}{retro_mark}{combust_mark}</td>'
        f'<td class="kmuted">{b["karaka"] or ""}</td>'
        f'<td class="kmuted">{karaka_meaning}</td>'
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

_scroll_target = st.session_state.pop("_scroll_to_section", None)
if _scroll_target:
    st.components.v1.html(
        f"""<script>
        var el = window.parent.document.getElementById('{_scroll_target}');
        if (el) {{ el.scrollIntoView({{behavior: 'smooth', block: 'start'}}); }}
        </script>""",
        height=0,
    )
