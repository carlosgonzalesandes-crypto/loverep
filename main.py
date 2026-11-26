#!/usr/bin/env python3
"""
LIVE RECORDER BOT
-----------------
Graba automáticamente los lives de Instagram de las cuentas que sigues,
en la máxima calidad disponible, y los sube a Telegram ordenados por
usuario (un "tema" por usuario) y por fecha (en el texto y hashtags).

Corre en GitHub Actions (ver .github/workflows/recorder.yml).
Todo el código está en este archivo para que puedas modificarlo fácil.
Las secciones están marcadas con  # ====  para que las encuentres rápido.
"""
import asyncio
import base64
import glob
import hashlib
import html
import json
import logging
import math
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import xml.etree.ElementTree as ET
from pathlib import Path
from urllib.parse import urljoin
from collections import deque
from datetime import datetime, timedelta
from types import SimpleNamespace
from zoneinfo import ZoneInfo

import requests
from cryptography.fernet import Fernet, InvalidToken
from telethon import Button, TelegramClient, events
from telethon.sessions import StringSession
from telethon.tl.functions.channels import GetChannelsRequest
from telethon.tl.types import DocumentAttributeVideo, InputChannel, InputPeerChannel

from instagrapi import Client as IGClient
from instagrapi.exceptions import BadPassword, ChallengeRequired, LoginRequired, TwoFactorRequired

try:
    from instagrapi.config import SUPPORTED_CAPABILITIES as _CAPS
except Exception:
    _CAPS = [
        {"name": "SUPPORTED_SDK_VERSIONS", "value": "13.0.0,14.0.0,15.0.0,16.0.0,17.0.0,18.0.0,19.0.0,20.0.0,21.0.0,22.0.0,23.0.0,24.0.0"},
        {"name": "FACE_TRACKER_VERSION", "value": "10"},
        {"name": "segmentation", "value": "segmentation_enabled"},
        {"name": "COMPRESSION", "value": "ETC2_COMPRESSION"},
        {"name": "world_tracker", "value": "world_tracker_enabled"},
        {"name": "gyroscope", "value": "gyroscope_enabled"},
    ]
CAPS_JSON = json.dumps(_CAPS)

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("rec")
logging.getLogger("telethon").setLevel(logging.WARNING)
logging.getLogger("instagrapi").setLevel(logging.WARNING)
logging.getLogger("private_request").setLevel(logging.WARNING)
logging.getLogger("public_request").setLevel(logging.WARNING)


def make_topic_request(chat, title):
    """Crea la petición de 'nuevo tema' sin depender de la versión de Telethon."""
    cls = None
    for mod in ("telethon.tl.functions.channels", "telethon.tl.functions.messages"):
        try:
            cls = getattr(__import__(mod, fromlist=["x"]), "CreateForumTopicRequest")
            break
        except (ImportError, AttributeError):
            continue
    if cls is None:
        raise RuntimeError("Esta versión de Telethon no soporta temas de foro")
    try:
        return cls(channel=chat, title=title)
    except TypeError:
        return cls(peer=chat, title=title)


LINK_RE = re.compile(r"https?://(?:www\.|m\.)?instagram\.com/[^\s]+", re.I)


def parse_target(text):
    """De un enlace de Instagram, @usuario o id devuelve (usuario, id_de_live)."""
    t = text.strip()
    username = bid = None
    m = LINK_RE.search(t)
    if m:
        url = m.group(0).split("?")[0].rstrip("/")
        parts = [p for p in url.split("instagram.com/", 1)[1].split("/") if p]
        for p in parts:
            if p.isdigit() and len(p) >= 12:
                bid = p
        skip = {"live", "stories", "p", "reel", "reels", "tv", "explore", "accounts", "s"}
        if parts and parts[0].lower() not in skip:
            username = parts[0]
        elif len(parts) > 1 and parts[0].lower() == "stories" and not parts[1].isdigit():
            username = parts[1]
    else:
        t = t.lstrip("@")
        if re.fullmatch(r"[A-Za-z0-9._]{1,30}", t) and not t.isdigit():
            username = t
        elif t.isdigit() and len(t) >= 12:
            bid = t
    return (username.lower() if username else None), bid


def classify_link(text):
    """Clasifica un enlace de Instagram: live, post/reel, historia, historias de un usuario o perfil."""
    t = text.strip()
    m = LINK_RE.search(t)
    if not m:
        user, bid = parse_target(t)
        if bid:
            return {"kind": "live", "user": user, "bid": bid, "url": None}
        if user:
            return {"kind": "profile", "user": user, "bid": None, "url": None}
        return {"kind": "none", "user": None, "bid": None, "url": None}
    url = m.group(0).split("?")[0].rstrip("/")
    parts = [p for p in url.split("instagram.com/", 1)[1].split("/") if p]
    low = [p.lower() for p in parts]
    user, bid = parse_target(m.group(0))
    link = {"kind": "none", "user": user, "bid": bid, "url": url}
    for marker in ("p", "reel", "reels", "tv"):
        if marker in low and low.index(marker) + 1 < len(parts):
            link["kind"] = "post"
            return link
    if low and low[0] == "stories":
        if len(parts) > 1 and low[1] == "highlights":
            link["kind"] = "highlight"
        elif len(parts) > 2 and parts[2].isdigit():
            link["kind"] = "story"
        elif len(parts) > 1:
            link["kind"] = "stories_user"
            link["user"] = parts[1].lower()
        return link
    if "live" in low or bid:
        link["kind"] = "live"
    elif parts:
        link["kind"] = "profile"
        link["user"] = parts[0].lower()
    return link


# ============================================================================
# CONFIGURACIÓN  (todo se puede cambiar desde los Secrets / variables del workflow)
# ============================================================================
def _env(name, default=None, required=False):
    v = os.environ.get(name, "").strip()
    if v:
        return v
    if required:
        sys.exit(f"❌ Falta el secret/variable {name}")
    return default


def load_config():
    return SimpleNamespace(
        api_id=int(_env("TG_API_ID", required=True)),
        api_hash=_env("TG_API_HASH", required=True),
        bot_token=_env("TG_BOT_TOKEN", required=True),
        chat_id=int(_env("TG_CHAT_ID", "0")),   # ya no se usa: todo llega a tu chat con el bot
        admin_id=int(_env("ADMIN_ID", required=True)),    # tu ID: solo tú puedes mandar comandos
        state_key=_env("STATE_KEY", required=True),       # clave para cifrar la sesión guardada
        ig_proxy=_env("IG_PROXY", ""),                    # opcional: http://user:pass@host:port
        tz=ZoneInfo(_env("TZ_NAME", "America/Lima")),     # tu zona horaria
        pick_batch=int(_env("PICK_BATCH", "10")),          # perfiles marcados revisados por ronda
        poll=int(_env("POLL_SECONDS", "45")),             # cada cuántos seg. busca lives nuevos
        max_runtime=int(_env("MAX_RUNTIME_MIN", "345")) * 60,  # turno de GitHub (máx 6h)
        segment=int(_env("SEGMENT_SECONDS", "3600")),     # un solo video por live hasta 1 hora
        part_max_bytes=int(_env("PART_MAX_MB", "1850")) * 1_000_000,  # tope por video (Telegram: 2 GB)
        backfill_max=int(_env("BACKFILL_SEGMENTS", "6000")),  # cuántos segmentos viejos bajar al detectar tarde
        data_dir=_env("DATA_DIR", "data"),
        rec_dir=_env("REC_DIR", "recordings"),
    )


CFG = None  # se carga en main()


# ============================================================================
# UTILIDADES
# ============================================================================
def safe(s):
    return re.sub(r"[^\w.\-]+", "_", s or "x")


def fmt_dur(sec):
    sec = int(sec)
    h, r = divmod(sec, 3600)
    m, s = divmod(r, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def fmt_size(b):
    for u in ("B", "KB", "MB", "GB"):
        if b < 1024 or u == "GB":
            return f"{b:.1f} {u}" if u != "B" else f"{int(b)} B"
        b /= 1024


async def run_cmd(*args, timeout=None):
    p = await asyncio.create_subprocess_exec(
        *args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
    )
    try:
        out, err = await asyncio.wait_for(p.communicate(), timeout)
    except asyncio.TimeoutError:
        p.kill()
        return -1, b"", b"timeout"
    return p.returncode, out, err


async def probe_video(path):
    """Devuelve (duración, ancho, alto) del video."""
    rc, out, _ = await run_cmd(
        "ffprobe", "-v", "error", "-select_streams", "v:0",
        "-show_entries", "stream=width,height:format=duration",
        "-of", "json", path, timeout=60,
    )
    try:
        j = json.loads(out)
        s = j["streams"][0]
        return float(j["format"]["duration"]), int(s["width"]), int(s["height"])
    except Exception:
        return 0.0, 0, 0


# ---------- DASH: lectura del manifiesto y descarga por segmentos numerados ----------
def _tag(el):
    return el.tag.split("}")[-1]


def _fill_template(tpl, rep, number=None, time_=None):
    out = tpl.replace("$RepresentationID$", str(rep["id"])).replace("$Bandwidth$", str(rep["bw"]))

    def sub(m):
        val = number if m.group(1) == "Number" else time_
        if val is None:
            return m.group(0)
        return (m.group(2) % val) if m.group(2) else str(val)

    out = re.sub(r"\$(Number|Time)(%0\d+d)?\$", sub, out)
    return out.replace("$$", "$")


def parse_mpd(xml_text, mpd_url):
    """Lee el manifiesto: representaciones de video/audio y su plantilla de segmentos."""
    root = ET.fromstring(xml_text)
    base = mpd_url
    for el in root:
        if _tag(el) == "BaseURL" and (el.text or "").strip():
            base = urljoin(mpd_url, el.text.strip())
            break
    info = {"dynamic": root.get("type") == "dynamic", "video": [], "audio": []}
    for aset in root.iter():
        if _tag(aset) != "AdaptationSet":
            continue
        a_tpl = next((c for c in aset if _tag(c) == "SegmentTemplate"), None)
        a_kind = (aset.get("contentType") or (aset.get("mimeType") or "").split("/")[0]).lower()
        for rep in aset:
            if _tag(rep) != "Representation":
                continue
            kind = (a_kind or (rep.get("mimeType") or "").split("/")[0]).lower()
            if kind not in ("video", "audio"):
                continue
            tpl = next((c for c in rep if _tag(c) == "SegmentTemplate"), None) or a_tpl
            if tpl is None or not tpl.get("media"):
                continue
            r = {
                "id": rep.get("id") or "0",
                "bw": int(rep.get("bandwidth") or 0),
                "w": int(rep.get("width") or 0),
                "h": int(rep.get("height") or 0),
                "start": int(tpl.get("startNumber") or 1),
                "timescale": int(tpl.get("timescale") or 1),
                "media": tpl.get("media"),
                "base": base,
                "timeline": [],
            }
            init = tpl.get("initialization")
            r["init"] = urljoin(base, _fill_template(init, r)) if init else None
            tl = next((c for c in tpl if _tag(c) == "SegmentTimeline"), None)
            if tl is not None:
                for s in tl:
                    if _tag(s) == "S":
                        r["timeline"].append((
                            int(s.get("t")) if s.get("t") is not None else None,
                            int(s.get("d") or 0),
                            int(s.get("r") or 0),
                        ))
            info[kind].append(r)
    return info


def list_segments(rep):
    """[(número, tiempo, duración)] de los segmentos que el manifiesto lista ahora."""
    out = []
    num = rep["start"]
    t = None
    for st, d, rr in rep["timeline"]:
        if st is not None:
            t = st
        elif t is None:
            t = 0
        for _ in range(rr + 1):
            out.append((num, t, d))
            num += 1
            t += d
    return out


def segment_url(rep, number, time_):
    return urljoin(rep["base"], _fill_template(rep["media"], rep, number, time_))


def http_get(session, url):
    try:
        r = session.get(url, timeout=20)
        return r.status_code, r.content
    except Exception:
        return 0, b""


def fetch_manifest(url):
    """Descarga el manifiesto (.mpd) del live. Devuelve (código HTTP, texto)."""
    import requests
    try:
        r = requests.get(url, timeout=15, headers={"User-Agent": "Mozilla/5.0"})
        return r.status_code, r.text
    except Exception as e:
        return 0, f"error: {e}"


def mask_urls(text):
    """Oculta las firmas de las direcciones para poder compartir el manifiesto."""
    return re.sub(r"\?[^\"'<>\s]+", "?…", text)


async def probe_manifest(url):
    """Lo que ffprobe ve en un manifiesto: mejor video y lista de resoluciones."""
    rc, out, _ = await run_cmd("ffprobe", "-v", "error", "-show_streams", "-of", "json", url, timeout=60)
    if rc != 0:
        return None
    try:
        vids = [s for s in json.loads(out)["streams"] if s.get("codec_type") == "video"]
    except Exception:
        return None
    if not vids:
        return None
    best = max(vids, key=lambda s: (int(s.get("width") or 0) * int(s.get("height") or 0),
                                    int(s.get("bit_rate") or 0)))
    return {
        "w": int(best.get("width") or 0), "h": int(best.get("height") or 0),
        "bw": int(best.get("bit_rate") or 0),
        "all": sorted({f"{s.get('width')}x{s.get('height')}" for s in vids}),
    }


async def pick_best_streams(url):
    """Elige el video de mayor resolución/bitrate y el mejor audio del manifiesto."""
    rc, out, probe_stderr = await run_cmd(
        "ffprobe", "-v", "error", "-show_streams", "-of", "json", url, timeout=90
    )
    v = a = None
    err = None if rc == 0 else (probe_stderr.decode(errors="ignore")[-400:] or f"ffprobe terminó con código {rc}")
    if rc == 0:
        try:
            streams = json.loads(out)["streams"]
            vids = [s for s in streams if s.get("codec_type") == "video"]
            auds = [s for s in streams if s.get("codec_type") == "audio"]
            if vids:
                v = max(
                    vids,
                    key=lambda s: (
                        int(s.get("width") or 0) * int(s.get("height") or 0),
                        int(s.get("bit_rate") or 0),
                    ),
                )["index"]
            if auds:
                a = max(auds, key=lambda s: int(s.get("bit_rate") or 0))["index"]
        except Exception:
            pass
    return v, a, err


# ============================================================================
# ESTADO CIFRADO (se guarda en la rama "state" de tu repo de GitHub)
# ============================================================================
class State:
    def __init__(self):
        self.path = os.path.join(CFG.data_dir, "state.enc")
        key = base64.urlsafe_b64encode(hashlib.sha256(CFG.state_key.encode()).digest())
        self.fernet = Fernet(key)
        self.lock = threading.Lock()
        self.data = {
            "ig_settings": None,   # sesión de Instagram
            "ig_user": None,
            "tg_session": "",      # sesión del bot de Telegram
            "topics": {},          # (en desuso)
            "library": {},         # usuario -> videos guardados en este chat (id, fecha, duración, peso)
            "only": [],            # si no está vacío: solo se graban estos
            "pks": {},             # usuario -> id numérico (caché)
            "following": None,     # cuántas cuentas sigues (se actualiza solo)
            "following_names": [], # lista de cuentas que sigues (para elegir perfiles)
            "picks": [],           # perfiles marcados para revisar uno por uno
        }
        self._load()

    def _load(self):
        if not os.path.exists(self.path):
            return
        try:
            raw = self.fernet.decrypt(open(self.path, "rb").read())
            self.data.update(json.loads(raw))
        except InvalidToken:
            sys.exit("❌ STATE_KEY distinta a la usada antes. Usa la misma o borra la rama 'state'.")

    def save(self, push=True):
        with self.lock:
            os.makedirs(CFG.data_dir, exist_ok=True)
            blob = self.fernet.encrypt(json.dumps(self.data).encode())
            tmp = self.path + ".tmp"
            with open(tmp, "wb") as f:
                f.write(blob)
            os.replace(tmp, self.path)
            if push:
                self._push()

    def _git(self, *args):
        return subprocess.run(["git", "-C", CFG.data_dir, *args], capture_output=True, text=True)

    def _push(self):
        if not os.path.isdir(os.path.join(CFG.data_dir, ".git")):
            return  # ejecución local sin git: solo guarda el archivo
        ident = ["-c", "user.name=recorder", "-c", "user.email=recorder@users.noreply.github.com"]
        self._git("add", "state.enc")
        has_head = self._git("rev-parse", "--verify", "HEAD").returncode == 0
        if has_head:
            self._git(*ident, "commit", "--amend", "-m", "state", "--allow-empty")
        else:
            self._git(*ident, "commit", "-m", "state", "--allow-empty")
        for i in range(3):
            r = self._git("push", "--force", "origin", "HEAD:state")
            if r.returncode == 0:
                return
            time.sleep(2 * (i + 1))
        log.warning("No pude subir el estado a GitHub: %s", r.stderr[-300:])


# ============================================================================
# INSTAGRAM
# ============================================================================
class Instagram:
    def __init__(self, state):
        self.state = state
        self.cl = None
        self.ok = False
        self.user = state.data.get("ig_user")
        self.last_info = None
        self._pick_idx = 0
        self._tray_variant = None
        self.following = state.data.get("following")
        self.following_time = None
        self._restore()

    def _new_client(self):
        cl = IGClient()
        cl.delay_range = [1, 3]
        if CFG.ig_proxy:
            cl.set_proxy(CFG.ig_proxy)
        return cl

    def _restore(self):
        s = self.state.data.get("ig_settings")
        if not s:
            return
        try:
            cl = self._new_client()
            cl.set_settings(s)
            self.cl, self.ok = cl, True
            log.info("Sesión de Instagram restaurada (@%s)", self.user)
        except Exception as e:
            log.warning("No pude restaurar la sesión de IG: %s", e)

    def _finish(self, cl):
        self.cl, self.ok = cl, True
        try:
            self.user = cl.account_info().username
        except Exception:
            self.user = self.user or getattr(cl, "username", None)
        self.persist()

    def persist(self):
        if self.cl:
            self.state.data["ig_settings"] = self.cl.get_settings()
            self.state.data["ig_user"] = self.user
            self.state.save()

    # --- login (corre en un hilo) ---
    def login(self, username, password, code=""):
        cl = self._new_client()
        try:
            if code:
                cl.login(username, password, verification_code=code)
            else:
                cl.login(username, password)
        except TwoFactorRequired:
            return False, "🔐 Tu cuenta tiene 2FA. Envía:\n/login usuario clave CODIGO_6_DIGITOS"
        except ChallengeRequired:
            return False, ("⚠️ Instagram pidió verificación (normal desde servidores de GitHub).\n"
                           "Usa mejor /sessionid (mira el README) o configura un IG_PROXY.")
        except BadPassword:
            return False, "❌ Usuario o contraseña incorrectos."
        except Exception as e:
            return False, f"❌ No se pudo iniciar sesión: {str(e)[:300]}"
        self._finish(cl)
        return True, f"✅ Sesión iniciada como @{self.user}. Ya busco lives de quienes sigues."

    def login_sessionid(self, sessionid):
        cl = self._new_client()
        try:
            cl.login_by_sessionid(sessionid)
        except Exception as e:
            return False, f"❌ sessionid inválido o vencido: {str(e)[:300]}"
        self._finish(cl)
        return True, f"✅ Sesión iniciada como @{self.user}. Ya busco lives de quienes sigues."

    # --- lives en vivo de las cuentas que sigues (corre en un hilo) ---
    def _fetch_tray(self, name):
        """Tres formas de pedir la bandeja de historias y lives. 'tray_post' es como lo hace la app."""
        cl = self.cl
        if name == "tray_get":
            return cl.private_request("feed/reels_tray/")
        if name == "tray_get_caps":
            return cl.private_request(
                "feed/reels_tray/",
                params={"supported_capabilities_new": CAPS_JSON, "reason": "pull_to_refresh"},
            )
        return cl.private_request(
            "feed/reels_tray/",
            data={
                "supported_capabilities_new": CAPS_JSON,
                "reason": "pull_to_refresh",
                "timezone_offset": "-18000",
                "tray_session_id": cl.generate_uuid(),
                "request_id": cl.generate_uuid(),
                "page_size": 50,
                "_uuid": cl.uuid,
                "_csrftoken": getattr(cl, "token", "") or "",
            },
            with_signature=False,
        )

    def _story_feed(self, pk):
        """Historias (y live, si lo hay) de una cuenta, pidiéndolo como la app."""
        return self.cl.private_request(
            f"feed/user/{pk}/story/", params={"supported_capabilities_new": CAPS_JSON}
        )

    @staticmethod
    def _parse_broadcast(b, default_user=None, via=None):
        owner = b.get("broadcast_owner") or b.get("owner") or b.get("user") or {}
        username = owner.get("username") or default_user
        status = b.get("broadcast_status")
        if status is not None and status not in ("active", "interrupted"):
            return None   # terminado, repetición, etc.
        url = b.get("dash_playback_url") or b.get("dash_abr_playback_url") or b.get("playback_url")
        if not (b.get("id") and username and url):
            return None
        return {
            "id": str(b["id"]),
            "username": username,
            "url": url,
            "abr": b.get("dash_abr_playback_url"),
            "title": b.get("broadcast_message") or "",
            "published": b.get("published_time"),
            "via": via,
        }

    @staticmethod
    def _describe(b):
        """Resumen de un live que no se pudo leer (para diagnóstico)."""
        return f"{b.get('id')}: claves={','.join(sorted(b.keys())[:30])}"

    def live_broadcasts(self):
        """Lista de lives de las cuentas que sigues (bandeja general de Instagram)."""
        found = {}
        info = {"time": time.time(), "endpoints": {}, "total": 0, "unparsed": [], "picks": []}
        tray_ok = False
        try:
            res, used = self._get_tray()
            if isinstance(res, dict):
                tray_ok = True
                raw = list(res.get("broadcasts") or [])
                for item in res.get("tray") or []:
                    if isinstance(item, dict) and item.get("broadcast"):
                        raw.append(item["broadcast"])
                n_ok = 0
                for b in raw:
                    parsed = self._parse_broadcast(b, via="bandeja")
                    if parsed:
                        found[parsed["id"]] = parsed
                        n_ok += 1
                    else:
                        info["unparsed"].append(self._describe(b))
                keys = ",".join(sorted(res.keys())[:6])
                info["endpoints"]["bandeja"] = f"ok ({used}) | lives={len(raw)} validos={n_ok} | tray={len(res.get('tray') or [])} | claves: {keys}"
            else:
                info["endpoints"]["bandeja"] = "respuesta vacia"
        except Exception as e:
            msg = str(e).lower()
            if any(k in msg for k in ("login_required", "checkpoint", "challenge_required")):
                raise
            info["endpoints"]["bandeja"] = "error: " + str(e)[:150]

        # Perfiles marcados: se revisan uno por uno (más rápido y seguro), en rotación
        picks = list(self.state.data.get("picks", []))
        picks_ok = False
        if picks:
            batch = []
            for _ in range(min(CFG.pick_batch, len(picks))):
                batch.append(picks[self._pick_idx % len(picks)])
                self._pick_idx += 1
            for u in dict.fromkeys(batch):
                try:
                    pk = self.state.data["pks"].get(u)
                    if not pk:
                        pk = str(self.cl.user_id_from_username(u))
                        self.state.data["pks"][u] = pk
                    res = self._story_feed(pk)
                    picks_ok = True
                    b = (res or {}).get("broadcast")
                    if b:
                        parsed = self._parse_broadcast(b, default_user=u, via="perfil")
                        if parsed:
                            found[parsed["id"]] = parsed
                            info["picks"].append(f"{u}: EN VIVO")
                        else:
                            info["picks"].append(f"{u}: live sin url")
                            info["unparsed"].append(self._describe(b))
                    else:
                        info["picks"].append(f"{u}: no esta en vivo")
                except Exception as e:
                    if self._is_login_error(e):
                        raise
                    info["picks"].append(f"{u}: error {str(e)[:70]}")

        info["total"] = len(found)
        self.last_info = info
        if not tray_ok and not picks_ok:
            raise RuntimeError("No pude leer Instagram: " + " | ".join(info["endpoints"].values())[:300])
        return list(found.values())


    @staticmethod
    def _is_login_error(e):
        msg = str(e).lower()
        return isinstance(e, LoginRequired) or any(
            k in msg for k in ("login_required", "checkpoint", "challenge_required")
        )

    def _tray_lives(self):
        res, _ = self._get_tray()
        out = []
        if isinstance(res, dict):
            raw = list(res.get("broadcasts") or [])
            for item in res.get("tray") or []:
                if isinstance(item, dict) and item.get("broadcast"):
                    raw.append(item["broadcast"])
            for b in raw:
                p = self._parse_broadcast(b, via="bandeja")
                if p:
                    out.append(p)
        return out

    def _get_tray(self):
        """Pide la bandeja probando las variantes; recuerda la que funciona."""
        order = [self._tray_variant] if self._tray_variant else ["tray_post", "tray_get_caps", "tray_get"]
        last_err = None
        for name in order:
            try:
                r = self._fetch_tray(name)
            except Exception as e:
                if self._is_login_error(e):
                    raise
                last_err = e
                continue
            if isinstance(r, dict) and ("broadcasts" in r or "tray" in r):
                self._tray_variant = name
                return r, name
        self._tray_variant = None
        if last_err is not None:
            raise last_err
        return None, None

    def deep_probe(self, picks):
        """Prueba varias rutas a la vez y cuenta qué ve cada una (para saber cuál detecta lives)."""
        cl = self.cl
        lines = []

        def owner_name(x):
            o = x.get("broadcast_owner") or x.get("owner") or x.get("user") or {}
            return o.get("username") or "?"

        def summarize(res):
            if not isinstance(res, dict):
                return "respuesta vacía"
            b = [x for x in (res.get("broadcasts") or []) if isinstance(x, dict)]
            tray = res.get("tray") or []
            tl = sum(1 for it in tray if isinstance(it, dict) and (it.get("broadcast") or it.get("live")))
            keys = ",".join(sorted(res.keys())[:8])
            return f"broadcasts={len(b)} {[owner_name(x) for x in b][:5]} | tray={len(tray)} (con live: {tl}) | claves: {keys}"

        for name, label in (
            ("tray_post", "A) bandeja POST, como la app"),
            ("tray_get_caps", "B) bandeja GET con capacidades"),
            ("tray_get", "C) bandeja GET simple (la que usaba antes)"),
        ):
            try:
                lines.append(f"{label}: {summarize(self._fetch_tray(name))}")
            except Exception as e:
                tag = "SESIÓN CAÍDA" if self._is_login_error(e) else "error"
                lines.append(f"{label}: {tag} {str(e)[:100]}")

        for u in picks[:8]:
            try:
                pk = self.state.data["pks"].get(u) or str(cl.user_id_from_username(u))
                self.state.data["pks"][u] = pk
            except Exception as e:
                lines.append(f"perfil @{u}: no pude obtener su id ({str(e)[:60]})")
                continue
            for tag, fn in (("D) con capacidades", lambda: self._story_feed(pk)),
                            ("E) sin capacidades (antes)", lambda: cl.private_request(f"feed/user/{pk}/story/"))):
                try:
                    r = fn()
                    b = (r or {}).get("broadcast")
                    state = "EN VIVO" if b else "sin live"
                    extra = ""
                    if b:
                        extra = " | url ok" if self._parse_broadcast(b, default_user=u) else " | live SIN url: " + self._describe(b)[:120]
                    lines.append(f"perfil @{u} {tag}: {state}{extra}")
                except Exception as e:
                    lines.append(f"perfil @{u} {tag}: error {str(e)[:80]}")

        try:
            r = cl.private_request("discover/top_live/")
            lines.append(f"F) lives populares (formato de prueba): {summarize(r)}")
            first = next((x for x in (r.get("broadcasts") or []) if isinstance(x, dict)), None) if isinstance(r, dict) else None
            if first:
                p = self._parse_broadcast(first)
                lines.append("   primer live: " + ("url ok" if p else "SIN url, claves: " + self._describe(first)[:150]))
                if first.get("id"):
                    lines.append(f"   ficha completa: {len(self.broadcast_urls(first['id']))} manifiesto(s)")
        except Exception as e:
            lines.append(f"F) lives populares: error {str(e)[:100]}")
        return lines

    def find_live(self, username=None, broadcast_id=None):
        """Busca un live concreto por id o por usuario. Devuelve (datos | None, mensaje)."""
        cl = self.cl
        errors = []
        if broadcast_id:
            try:
                res = cl.private_request(f"live/{broadcast_id}/info/")
                b = self._parse_broadcast(res, default_user=username, via="id")
                if b:
                    return b, "ok"
                if isinstance(res, dict) and res.get("broadcast_status") not in (None, "active", "interrupted"):
                    return None, "Ese live ya terminó."
                errors.append("sin enlace de video")
            except Exception as e:
                if self._is_login_error(e):
                    raise
                errors.append("info: " + str(e)[:100])
        if username:
            try:
                for b in self._tray_lives():
                    if b["username"].lower() == username:
                        return b, "ok"
            except Exception as e:
                if self._is_login_error(e):
                    raise
                errors.append("bandeja: " + str(e)[:100])
            try:
                pk = self.state.data["pks"].get(username)
                if not pk:
                    pk = str(cl.user_id_from_username(username))
                    self.state.data["pks"][username] = pk
                res = self._story_feed(pk)
                b = (res or {}).get("broadcast")
                if b:
                    p = self._parse_broadcast(b, default_user=username, via="perfil")
                    if p:
                        return p, "ok"
            except Exception as e:
                if self._is_login_error(e):
                    raise
                errors.append("cuenta: " + str(e)[:100])
        who = f" de @{username}" if username else ""
        detail = f" ({'; '.join(errors)})" if errors else ""
        return None, f"No encontré un live activo{who} en este momento.{detail}"

    def broadcast_urls(self, bid):
        """Todas las direcciones de manifiesto que Instagram da para un live (ficha completa)."""
        try:
            res = self.cl.private_request(f"live/{bid}/info/")
        except Exception as e:
            if self._is_login_error(e):
                raise
            return []
        urls = []
        if isinstance(res, dict):
            for k, v in res.items():
                if k.startswith("dash") and k.endswith("url") and isinstance(v, str) and v.startswith("http"):
                    urls.append(v)
        return list(dict.fromkeys(urls))

    def broadcast_alive(self, bid):
        """True/False si el live sigue activo; None si no se pudo saber."""
        try:
            res = self.cl.private_request(f"live/{bid}/info/")
        except Exception:
            return None
        if not isinstance(res, dict) or res.get("broadcast_status") is None:
            return None
        return res["broadcast_status"] in ("active", "interrupted")


    def fetch_following_list(self):
        """Descarga la lista de cuentas que sigues (para elegir cuáles marcar)."""
        users = self.cl.user_following(self.cl.user_id, use_cache=False)
        names = {}
        for pk, u in users.items():
            if getattr(u, "username", None):
                names[u.username.lower()] = str(pk)
        self.state.data["pks"].update(names)
        self.state.data["following_names"] = sorted(names)
        self.state.save()
        return len(names)

    def fetch_content(self, link, workdir):
        """Descarga historias, publicaciones, reels y álbumes. Devuelve [{path, type, user}]."""
        cl = self.cl
        wd = Path(workdir)
        wd.mkdir(parents=True, exist_ok=True)
        out = []
        kind = link["kind"]
        if kind == "post":
            pk = cl.media_pk_from_url(link["url"])
            info = cl.media_info(pk)
            user = info.user.username
            if info.media_type == 1:
                out.append({"path": str(cl.photo_download(pk, folder=wd)), "type": "foto", "user": user})
            elif info.media_type == 2:
                kind_txt = "reel" if "reel" in link["url"] else "video"
                out.append({"path": str(cl.video_download(pk, folder=wd)), "type": kind_txt, "user": user})
            elif info.media_type == 8:
                for p in cl.album_download(pk, folder=wd):
                    out.append({"path": str(p), "type": "álbum", "user": user})
        elif kind == "story":
            spk = cl.story_pk_from_url(link["url"])
            info = cl.story_info(spk)
            out.append({"path": str(cl.story_download(spk, folder=wd)), "type": "historia",
                        "user": info.user.username})
        elif kind == "stories_user":
            uid = cl.user_id_from_username(link["user"])
            for st in cl.user_stories(uid):
                out.append({"path": str(cl.story_download(st.pk, folder=wd)), "type": "historia",
                            "user": link["user"]})
        return out

    def account_details(self, username):
        """Datos públicos de una cuenta: seguidores, publicaciones, etc."""
        u = self.cl.user_info_by_username_v1(username)
        try:
            self.state.data["pks"][username] = str(u.pk)
        except Exception:
            pass
        return {
            "user": u.username, "name": u.full_name or "", "bio": u.biography or "",
            "followers": u.follower_count, "following": u.following_count, "posts": u.media_count,
            "private": bool(u.is_private), "verified": bool(u.is_verified),
            "category": getattr(u, "category", None) or "",
            "url": str(getattr(u, "external_url", None) or ""),
        }

    def refresh_following(self):
        """Cuántas cuentas sigues ahora mismo (None si no se pudo saber)."""
        try:
            info = self.cl.user_info_v1(self.cl.user_id)
            n = int(info.following_count)
            if not self.user and getattr(info, "username", None):
                self.user = info.username
                self.state.data["ig_user"] = self.user
        except Exception as e:
            if self._is_login_error(e):
                raise
            log.warning("No pude leer cuántas cuentas sigues: %s", e)
            return None
        self.following = n
        self.following_time = time.time()
        return n


# ============================================================================
# GRABACIÓN DE UN LIVE  (ffmpeg, calidad máxima, sin recomprimir)
# ============================================================================
class Recording:
    def __init__(self, app, b, manual=False):
        self.app = app
        self.b = b
        self.manual = manual
        self.user = b["username"]
        self.id = b["id"]
        self.start = datetime.now(CFG.tz)
        self.dir = os.path.join(
            CFG.rec_dir, safe(self.user),
            self.start.strftime("%Y-%m-%d_%H%M%S") + "_" + self.id[-6:],
        )
        self.proc = None
        self.stop_flag = False
        self.missing = 0
        self.cum = 0.0      # segundos ya subidos (para la hora de cada parte)
        self.part = 0
        self.sent = 0
        self.task = None
        self.t0 = time.time()
        self.tail = deque(maxlen=15)
        self.via = b.get("via")
        self.fail_reason = None
        self.probe_err = None
        self.mpd_head = ""
        self.dropped = []
        self.upload_failed = False
        self.rc = None
        self.method = None            # "segmentos" o "ffmpeg"
        self.dash_note = None
        self.published = b.get("published")
        self.quality = None            # calidad elegida (resolución · bitrate)
        self.qual_options = []         # resoluciones disponibles en el manifiesto
        self.manifest_choice = "principal"
        self.n_manifests = 0
        self.force_ffmpeg = False
        self.live_start = None
        self.rec_seconds = 0.0
        self._upl_tasks = []
        self.finished = False
        self.uploading = 0
        self.status_msg = None
        self.status_task = None

    def failure_text(self, ran):
        reason = self.fail_reason
        if not reason:
            if self.upload_failed:
                reason = "no se pudo subir el video a Telegram"
            elif self.dropped:
                reason = "el video quedó demasiado corto (" + ", ".join(self.dropped) + ")"
            else:
                reason = f"ffmpeg terminó sin producir video (código {self.rc})"
        lines = [
            f"⚠️ No pude grabar el live de @{self.user} (estuve {fmt_dur(ran)} intentándolo).",
            f"Motivo: {reason}",
            f"Detectado por: {self.via or '?'}",
            f"Método: {self.method or 'sin iniciar'}",
            f"Calidad elegida: {self.quality or '?'} (manifiesto {self.manifest_choice})",
        ]
        if self.dash_note:
            lines.append("Segmentos: " + self.dash_note)
        if self.probe_err:
            lines.append("ffprobe: " + self.probe_err.strip()[-300:])
        if self.tail:
            lines.append("ffmpeg: " + " | ".join(self.tail)[-500:])
        if self.mpd_head:
            lines.append("Manifiesto (recortado):\n" + self.mpd_head)
        lines.append("Mándale este mensaje a Claude para arreglarlo.")
        return "\n".join(lines)[:3800]

    def request_stop(self):
        self.stop_flag = True
        if self.proc and self.proc.returncode is None:
            try:
                self.proc.stdin.write(b"q")   # ffmpeg cierra el archivo limpio
            except Exception:
                pass

    async def _drain_err(self):
        try:
            while True:
                line = await self.proc.stderr.readline()
                if not line:
                    break
                self.tail.append(line.decode(errors="ignore").strip())
        except Exception:
            pass

    def recorded_seconds(self):
        if self.method == "segmentos":
            return self.rec_seconds
        return time.time() - self.t0

    def airtime(self):
        """Cuánto lleva el live desde que empezó (None si Instagram no dio la hora de inicio)."""
        if self.published:
            return max(0.0, time.time() - float(self.published))
        if self.method == "segmentos":
            return self.rec_seconds
        return None

    async def run(self):
        os.makedirs(self.dir, exist_ok=True)
        url = self.b["url"]
        status, mpd = await asyncio.to_thread(fetch_manifest, url)
        self.mpd_head = mask_urls(mpd[:1800])
        if status != 200:
            self.fail_reason = f"el manifiesto del live respondió {status}"
            shutil.rmtree(self.dir, ignore_errors=True)
            return
        if 'type="static"' in mpd:
            self.fail_reason = "el live ya había terminado (manifiesto estático)"
            shutil.rmtree(self.dir, ignore_errors=True)
            return
        url, mpd = await self._pick_best_manifest(url, mpd)
        order = ["ffmpeg", "dash"] if self.force_ffmpeg else ["dash", "ffmpeg"]
        for m in order:
            if self.stop_flag:
                break
            recorded = False
            try:
                if m == "dash":
                    recorded = await self._run_dash(url, mpd)
                else:
                    self.method = "ffmpeg"
                    await self._run_ffmpeg(url)
                    recorded = bool(self.sent or self.part or self.dropped)
            except Exception as e:
                self.dash_note = f"error ({m}): {str(e)[:200]}"
                log.exception("Fallo la grabación (%s) de @%s", m, self.user)
            if recorded:
                break
        if self._upl_tasks:
            await asyncio.gather(*self._upl_tasks, return_exceptions=True)
        shutil.rmtree(self.dir, ignore_errors=True)

    async def _pick_best_manifest(self, url, mpd):
        """Prueba todos los manifiestos del live (con mi lector y con ffprobe) y usa el de mejor calidad."""
        def parse_best(text, u):
            try:
                reps = parse_mpd(text, u)["video"]
            except Exception:
                return None, []
            if not reps:
                return None, []
            return max(reps, key=lambda r: (r["w"] * r["h"], r["bw"])), reps

        def sc(w, h, bw):
            return (w * h, bw)

        urls = [url, self.b.get("abr")]
        ig = getattr(self.app, "ig", None)
        if ig is not None:
            try:
                urls += await asyncio.to_thread(ig.broadcast_urls, self.id)
            except Exception as e:
                log.warning("No pude pedir la ficha completa del live: %s", e)

        cands, report, seen = [], [], set()
        for i, u in enumerate(urls):
            if not u or u in seen:
                continue
            seen.add(u)
            if u == url:
                st, text = 200, mpd
            else:
                st, text = await asyncio.to_thread(fetch_manifest, u)
            name = f"manifiesto {len(cands) + 1}"
            if st != 200 or 'type="static"' in text:
                report.append(f"{name}: no disponible (HTTP {st})")
                continue
            pb, reps = parse_best(text, u)
            fp = await probe_manifest(u)
            p_sc = sc(pb["w"], pb["h"], pb["bw"]) if pb else (0, 0)
            f_sc = sc(fp["w"], fp["h"], fp["bw"]) if fp else (0, 0)
            line = f"{name}: lector={'%dx%d' % (pb['w'], pb['h']) if pb else 'no pudo leerlo'}"
            line += f" | ffprobe={', '.join(fp['all']) if fp else 'no pudo leerlo'}"
            if not pb:
                line += "\n   inicio: " + mask_urls(text[:500]).replace("\n", " ")
            report.append(line)
            cands.append({"url": u, "mpd": text, "pb": pb, "reps": reps, "fp": fp,
                          "score": max(p_sc, f_sc), "ffmpeg_better": f_sc > p_sc})
        if cands:
            top = max(cands, key=lambda c: c["score"])
            self.n_manifests = len(cands)
            if top["url"] != url:
                self.manifest_choice = "otro"
            url, mpd = top["url"], top["mpd"]
            self.force_ffmpeg = top["ffmpeg_better"]
            src = top["fp"] if (top["ffmpeg_better"] and top["fp"]) else (top["pb"] or top["fp"])
            if src:
                self.quality = f"{src['w']}x{src['h']} · {src['bw'] / 1e6:.1f} Mbps"
            opts = set()
            for r in top["reps"]:
                opts.add(f"{r['w']}x{r['h']}")
            if top["fp"]:
                opts.update(top["fp"]["all"])
            self.qual_options = sorted(opts)
        try:
            await self.app.notify(
                f"📋 Calidad del live de @{self.user}: elegí {self.quality or '?'}"
                f"{' (con ffmpeg)' if self.force_ffmpeg else ''}\n" + "\n".join(report)
            )
        except Exception:
            pass
        return url, mpd

    # ---- método principal: bajar los segmentos numerados (desde el inicio del live) ----
    async def _run_dash(self, url, mpd_text):
        info = parse_mpd(mpd_text, url)
        if not info["video"]:
            self.dash_note = "el manifiesto no trae video con segmentos"
            return False
        vrep = max(info["video"], key=lambda r: (r["w"] * r["h"], r["bw"]))
        arep = max(info["audio"], key=lambda r: r["bw"]) if info["audio"] else None
        vsegs = list_segments(vrep)
        if not vsegs:
            self.dash_note = "no pude leer la lista de segmentos del manifiesto"
            return False
        ts = vrep["timescale"] or 1
        sess = requests.Session()
        sess.headers["User-Agent"] = "Mozilla/5.0"
        segdir = os.path.join(self.dir, "seg")
        os.makedirs(segdir, exist_ok=True)
        last_code = {"v": None}

        async def dl(u, path):
            code, data = await asyncio.to_thread(http_get, sess, u)
            last_code["v"] = code
            if code == 200 and data:
                with open(path, "wb") as f:
                    f.write(data)
                return len(data)
            return False

        vinit = os.path.join(segdir, "v_init")
        ainit = os.path.join(segdir, "a_init")
        if not (vrep["init"] and await dl(vrep["init"], vinit)):
            self.dash_note = f"no pude bajar el encabezado del video (HTTP {last_code['v']})"
            return False
        if arep and not (arep["init"] and await dl(arep["init"], ainit)):
            arep = None   # sin audio
        a_map = {n: t for n, t, _ in list_segments(arep)} if arep else {}

        done = {}   # número -> {"v": ruta, "a": ruta|None, "dur": segundos}

        async def grab(num, t, dur):
            vp = os.path.join(segdir, f"v_{num:09d}")
            vsz = await dl(segment_url(vrep, num, t), vp)
            if not vsz:
                return False
            ap, asz = None, 0
            if arep:
                ap = os.path.join(segdir, f"a_{num:09d}")
                asz = await dl(segment_url(arep, num, a_map.get(num)), ap)
                if not asz:
                    os.remove(vp)
                    return False
            done[num] = {"v": vp, "a": ap, "dur": dur, "size": vsz + asz}
            return True

        # 1) hacia atrás: los segmentos anteriores siguen disponibles por número
        first = vsegs[0][0]
        typical = vsegs[0][2] / ts
        can_back = "$Number" in vrep["media"] and (arep is None or "$Number" in arep["media"])
        if can_back:
            n, got = first - 1, 0
            while n >= 0 and got < CFG.backfill_max and not self.stop_flag:
                batch = list(range(n, max(n - 6, -1), -1))
                res = await asyncio.gather(*[grab(x, None, typical) for x in batch])
                got += sum(1 for r in res if r)
                self.rec_seconds = sum(x["dur"] for x in done.values())
                if not all(res):
                    break
                n = batch[-1] - 1
        back_secs = sum(x["dur"] for x in done.values())
        if self.published:
            self.live_start = datetime.fromtimestamp(float(self.published), CFG.tz)
        else:
            self.live_start = self.start - timedelta(seconds=back_secs)
        if done:
            self.method = "segmentos"

        # 2) hacia adelante: lo que lista el manifiesto, hasta que el live termine
        asm_next = min(done) if done else first
        cum = 0.0
        cur, dynamic = vsegs, info["dynamic"]
        fails, misses = {}, 0
        t_start = last_new = time.time()
        while True:
            for num, t, d in cur:
                if num in done or num < asm_next:
                    continue
                if await grab(num, t, d / ts):
                    self.method = "segmentos"
                    last_new = time.time()
                else:
                    fails[num] = fails.get(num, 0) + 1
                    if fails[num] >= 6:
                        done[num] = {"v": None, "a": None, "dur": 0, "size": 0}   # hueco irrecuperable
                    else:
                        break
            self.rec_seconds = sum(x["dur"] for x in done.values()) + cum
            cum, asm_next = await self._assemble_ready(done, asm_next, cum, vinit, ainit if arep else None, False)
            if self.method != "segmentos" and time.time() - t_start > 40:
                self.dash_note = f"no pude bajar segmentos (HTTP {last_code['v']})"
                return False
            if self.stop_flag or not dynamic:
                break
            if time.time() - last_new > 90:
                break   # el live dejó de enviar video
            await asyncio.sleep(2)
            code, text = await asyncio.to_thread(fetch_manifest, url)
            if code != 200:
                misses += 1
                if misses >= 5:
                    break
                continue
            misses = 0
            try:
                info2 = parse_mpd(text, url)
                nv = next((r for r in info2["video"] if r["id"] == vrep["id"]), None)
                if nv:
                    cur, dynamic = list_segments(nv), info2["dynamic"]
                    if arep:
                        na = next((r for r in info2["audio"] if r["id"] == arep["id"]), None)
                        if na:
                            a_map = {n: t for n, t, _ in list_segments(na)}
            except Exception:
                pass
        await self._assemble_ready(done, asm_next, cum, vinit, ainit if arep else None, True)
        return self.method == "segmentos"

    async def _assemble_ready(self, done, asm_next, cum, vinit, ainit, final):
        """Junta los segmentos en un video: se corta al llegar a 1 hora o al tope de tamaño de Telegram."""
        while True:
            nums, acc, size, n, reached = [], 0.0, 0, asm_next, False
            while n in done:
                nums.append(n)
                acc += done[n]["dur"]
                size += done[n].get("size", 0)
                n += 1
                if acc >= CFG.segment or size >= CFG.part_max_bytes:
                    reached = True
                    break
            if not nums or (not reached and not final):
                break
            await self._assemble(nums, done, vinit, ainit, cum)
            cum += acc
            asm_next = n
            for k in nums:
                done.pop(k, None)
            if final and n not in done:
                break
        return cum, asm_next

    async def _assemble(self, nums, done, vinit, ainit, cum):
        self.part += 1
        idx = self.part
        vcat = os.path.join(self.dir, f"c{idx:03d}_v.mp4")
        acat = os.path.join(self.dir, f"c{idx:03d}_a.mp4") if ainit else None

        def build():
            for cat, init, key in ((vcat, vinit, "v"), (acat, ainit, "a")):
                if not cat:
                    continue
                with open(cat, "wb") as out:
                    with open(init, "rb") as f:
                        shutil.copyfileobj(f, out)
                    for n in nums:
                        p = done[n][key]
                        if p:
                            with open(p, "rb") as f:
                                shutil.copyfileobj(f, out)

        await asyncio.to_thread(build)
        out = os.path.join(self.dir, f"part_{idx:03d}.mp4")
        cmd = ["ffmpeg", "-v", "error", "-y", "-i", vcat]
        if acat:
            cmd += ["-i", acat]
        cmd += ["-c", "copy", "-movflags", "+faststart", "-avoid_negative_ts", "make_zero", out]
        rc, _, err = await run_cmd(*cmd)
        for n in nums:
            for key in ("v", "a"):
                p = done[n][key]
                if p and os.path.exists(p):
                    os.remove(p)
        for cat in (vcat, acat):
            if cat and os.path.exists(cat):
                os.remove(cat)
        if rc != 0 or not os.path.exists(out):
            self.dash_note = "no pude unir video y audio: " + err.decode(errors="ignore")[-200:]
            log.warning("Fallo al unir la parte %d de @%s: %s", idx, self.user, self.dash_note)
            return
        part_start = (self.live_start or self.start) + timedelta(seconds=cum)
        self._upl_tasks.append(asyncio.create_task(self._upload(out, part_start=part_start, part_no=idx)))

    # ---- método de respaldo: ffmpeg lee el manifiesto directamente ----
    async def _run_ffmpeg(self, url):
        v, a, self.probe_err = await pick_best_streams(url)
        maps = []
        if v is not None:
            maps += ["-map", f"0:{v}"]
        if a is not None:
            maps += ["-map", f"0:{a}"]
        log.info("Grabando @%s con ffmpeg (video stream %s, audio stream %s)", self.user, v, a)

        cmd = [
            "ffmpeg", "-hide_banner", "-loglevel", "warning", "-y",
            "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "10",
            "-i", url, *maps, "-c", "copy",   # copy = calidad original, sin perder nada
            "-f", "segment", "-segment_time", str(CFG.segment),
            "-segment_format", "matroska", "-reset_timestamps", "1",
            os.path.join(self.dir, "part_%03d.mkv"),
        ]
        self.proc = await asyncio.create_subprocess_exec(
            *cmd, stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
        )
        err_task = asyncio.create_task(self._drain_err())
        stop_since = None
        while self.proc.returncode is None:
            try:
                await asyncio.wait_for(self.proc.wait(), 15)
            except asyncio.TimeoutError:
                pass
            await self._upload_ready(final=False)
            if self.stop_flag:
                stop_since = stop_since or time.time()
                if time.time() - stop_since > 45 and self.proc.returncode is None:
                    self.proc.terminate()
        await err_task
        self.rc = self.proc.returncode
        if self.tail and not glob.glob(os.path.join(self.dir, "part_*.mkv")):
            log.warning("ffmpeg falló para @%s: %s", self.user, " | ".join(self.tail)[-400:])
        await self._upload_ready(final=True)

    async def _upload_ready(self, final):
        files = sorted(glob.glob(os.path.join(self.dir, "part_*.mkv")))
        ready = files if final else files[:-1]   # la última parte aún se está escribiendo
        for f in ready:
            await self._upload(f)

    async def _upload(self, src, part_start=None, part_no=None):
        if src.endswith(".mkv"):
            mp4 = src[:-4] + ".mp4"
            rc, _, err = await run_cmd(
                "ffmpeg", "-v", "error", "-y", "-i", src, "-c", "copy", "-movflags", "+faststart", mp4
            )
            if rc != 0 or not os.path.exists(mp4):
                log.warning("No pude convertir %s: %s", src, err[-200:])
                os.rename(src, src + ".bad")
                return
            os.remove(src)
        else:
            mp4 = src
        dur, w, h = await probe_video(mp4)
        if dur < 3 or os.path.getsize(mp4) < 150_000:
            self.dropped.append(f"{dur:.1f}s, {fmt_size(os.path.getsize(mp4))}")
            os.remove(mp4)
            return

        if part_start is None:
            part_start = self.start + timedelta(seconds=self.cum)
            self.cum += dur
            self.part += 1
            part_no = self.part

        # Si por alguna razón pesa más de ~1.9GB, se divide (límite de Telegram: 2GB)
        pieces = [mp4]
        if os.path.getsize(mp4) > 1_900_000_000:
            n = math.ceil(os.path.getsize(mp4) / 1_800_000_000)
            seg = int(dur / n) + 1
            pat = mp4[:-4] + "_p%02d.mp4"
            rc, _, _ = await run_cmd(
                "ffmpeg", "-v", "error", "-y", "-i", mp4, "-c", "copy",
                "-f", "segment", "-segment_time", str(seg), "-reset_timestamps", "1",
                "-movflags", "+faststart", pat,
            )
            if rc == 0:
                pieces = sorted(glob.glob(mp4[:-4] + "_p*.mp4"))
                os.remove(mp4)

        for i, p in enumerate(pieces):
            d, pw, ph = await probe_video(p)
            thumb = p[:-4] + ".jpg"
            await run_cmd(
                "ffmpeg", "-v", "error", "-y", "-ss", "1", "-i", p,
                "-frames:v", "1", "-vf", "scale=320:-1", thumb,
            )
            if not os.path.exists(thumb):
                thumb = None
            tag_user = re.sub(r"\W+", "_", self.user)
            tag_date = part_start.strftime("%Y_%m_%d")
            extra = f" · parte {part_no}" + (f".{i + 1}" if len(pieces) > 1 else "")
            caption = (
                f"🔴 @{self.user}\n"
                f"📅 {part_start.strftime('%Y-%m-%d · %H:%M')} ({CFG.tz.key})\n"
                f"⏱ {fmt_dur(d)} · 📦 {fmt_size(os.path.getsize(p))} · 📺 {pw}x{ph}{extra}\n"
                f"#{tag_user} #{tag_date}"
            )
            self.uploading += 1
            try:
                meta = {"kind": "live", "when": part_start.isoformat(), "size": os.path.getsize(p),
                        "part": (f"{part_no}.{i + 1}" if len(pieces) > 1 else part_no)}
                ok = await self.app.upload_video(self.user, p, caption, d, pw, ph, thumb, meta)
            finally:
                self.uploading -= 1
            if ok:
                self.sent += 1
                os.remove(p)
                if thumb:
                    os.remove(thumb)
            else:
                self.upload_failed = True
                os.makedirs(os.path.join(CFG.rec_dir, "_fallidos"), exist_ok=True)
                shutil.move(p, os.path.join(CFG.rec_dir, "_fallidos", os.path.basename(p)))
                await self.app.notify(f"⚠️ No pude subir una parte del live de @{self.user}.")


# ============================================================================
# APP PRINCIPAL: Telegram + bucle que busca lives
# ============================================================================
class App:
    def __init__(self):
        self.state = State()
        self.ig = Instagram(self.state)
        self.client = TelegramClient(
            StringSession(self.state.data.get("tg_session", "")), CFG.api_id, CFG.api_hash
        )
        self.chat = None
        self.tz = CFG.tz
        self.t0 = time.time()
        self.active = {}          # id del live -> Recording
        self.cooldown = {}        # id del live -> timestamp hasta el que no reintenta
        self.notified = set()
        self.stop_event = asyncio.Event()
        self.topic_lock = asyncio.Lock()
        self.upload_sem = asyncio.Semaphore(2)
        self.use_topics = False    # todo llega al chat privado con el bot
        self.session_alert_sent = False
        self.pending = None       # lo que espera el menú (enlace, usuarios…)
        self.unparsed_seen = set()
        self.fail_count = {}
        self.fail_notified = set()
        self.last_sent = None
        self.acc_cache = {}
        self.client.parse_mode = "html"

    # ---------- Telegram ----------
    async def notify(self, text):
        try:
            await self.client.send_message(CFG.admin_id, text, parse_mode=None)
        except Exception as e:
            log.warning("No pude avisar al admin: %s", e)

    async def resolve_chat(self):
        try:
            return await self.client.get_input_entity(CFG.chat_id)
        except Exception:
            pass
        try:
            cid = int(str(CFG.chat_id).replace("-100", "", 1))
            r = await self.client(GetChannelsRequest([InputChannel(cid, 0)]))
            ch = r.chats[0]
            return InputPeerChannel(ch.id, ch.access_hash)
        except Exception as e:
            sys.exit(f"❌ No encuentro el grupo {CFG.chat_id}. ¿El bot está dentro y es admin? ({e})")

    async def ensure_topic(self, user):
        async with self.topic_lock:
            if not self.use_topics:
                return None
            topics = self.state.data["topics"]
            if user in topics:
                return topics[user]
            try:
                res = await self.client(make_topic_request(self.chat, f"@{user}"))
                tid = None
                for u in getattr(res, "updates", []):
                    m = getattr(u, "message", None)
                    if m is not None and getattr(m, "id", None):
                        tid = m.id
                        break
                if tid is None:
                    for u in getattr(res, "updates", []):
                        if u.__class__.__name__ == "UpdateMessageID":
                            tid = u.id
                if tid is None:
                    raise RuntimeError("no obtuve el id del tema")
                topics[user] = tid
                await asyncio.to_thread(self.state.save)
                return tid
            except Exception as e:
                self.use_topics = False
                await self.notify(
                    "⚠️ No pude crear temas por usuario en el grupo.\n"
                    "Activa 'Temas' en el grupo y da al bot permiso 'Administrar temas'.\n"
                    f"Mientras tanto subo todo al chat general con hashtags. ({str(e)[:150]})"
                )
                return None

    async def upload_video(self, user, path, caption, dur, w, h, thumb, meta=None):
        async with self.upload_sem:
            for attempt in range(1, 4):
                try:
                    tid = await self.ensure_topic(user)
                    sent = await self.client.send_file(
                        self.chat, path, caption=caption, thumb=thumb, reply_to=tid,
                        attributes=[DocumentAttributeVideo(
                            duration=int(dur), w=w, h=h, supports_streaming=True)],
                        force_document=False, part_size_kb=512, parse_mode=None,
                    )
                    self.last_sent = sent
                    if meta:
                        await self.library_add(user, sent, dur, meta)
                    return True
                except Exception as e:
                    log.warning("Subida falló (intento %d): %s", attempt, e)
                    await asyncio.sleep(5 * attempt)
            return False

    # ---------- filtros ----------
    def allowed(self, user):
        u = user.lower()
        d = self.state.data
        return (not d["only"]) or (u in d["only"])

    # ---------- enlaces / búsqueda manual ----------
    async def record_target(self, text):
        """Graba un live a partir de un enlace de Instagram, @usuario o id. Devuelve el texto de respuesta."""
        if not self.ig.ok:
            return "❌ Primero inicia sesión en Instagram (menú → 🔑 Sesión IG)."
        user, bid = parse_target(text)
        if not user and not bid:
            return "❌ No entendí el enlace. Envía un enlace de Instagram o el @usuario."
        if bid and bid in self.active:
            return "ℹ️ Ese live ya se está grabando."
        try:
            b, note = await asyncio.to_thread(self.ig.find_live, user, bid)
        except Exception as e:
            return "❌ Error consultando Instagram: " + html.escape(str(e)[:200])
        if not b:
            return "⚪ " + html.escape(note) + "\nLos lives de las cuentas que sigues se graban solos cuando empiezan."
        if b["id"] in self.active:
            return "ℹ️ Ese live ya se está grabando."
        status, mpd = await asyncio.to_thread(fetch_manifest, b["url"])
        if status != 200:
            return (f"⚪ Encontré el live de @{html.escape(b['username'])}, pero su video ya no responde "
                    f"(código {status}). Probablemente ya terminó.")
        if 'type="static"' in mpd:
            return f"⚪ El live de @{html.escape(b['username'])} ya terminó, no se puede grabar en directo."
        rec = Recording(self, b, manual=True)
        self.active[b["id"]] = rec
        rec.task = asyncio.create_task(self._run_rec(rec))
        self.notified.add(b["id"])
        return (f"🔴 Grabando el live de @{html.escape(b['username'])} en máxima calidad…\n"
                f"(encontrado por: {html.escape(str(b.get('via') or '?'))})\n"
                "El video llega a este chat cuando termine el live. Si algo falla, te aviso aquí.")

    # ---------- conteo de cuentas que sigues (automático) ----------
    async def refresh_following(self, force=False):
        if not self.ig.ok:
            return
        if not force and self.ig.following_time and time.time() - self.ig.following_time < 300:
            return
        try:
            n = await asyncio.to_thread(self.ig.refresh_following)
        except Exception:
            return
        if n is None:
            return
        prev = self.state.data.get("following")
        if prev is not None and n != prev:
            diff = n - prev
            signo = "+" if diff > 0 else ""
            await self.notify(f"👥 Cambió la cantidad de cuentas que sigues: {prev} → {n} ({signo}{diff})")
        if n != prev:
            self.state.data["following"] = n
            await asyncio.to_thread(self.state.save)

    def following_line(self):
        n = self.ig.following
        if n is None:
            return "👥 Siguiendo a: — (aún sin consultar)"
        age = ""
        if self.ig.following_time:
            age = f" · actualizado hace {int((time.time() - self.ig.following_time) / 60)} min"
        return f"👥 Siguiendo a: <b>{n}</b> cuentas{age}"

    # ---------- cronómetro de cada grabación ----------
    def rec_line(self, r):
        parts = [f"⏱ grabado {fmt_dur(r.recorded_seconds())}"]
        at = r.airtime()
        if at:
            parts.append(f"live {fmt_dur(at)}")
        return f"@{html.escape(r.user)} – " + " · ".join(parts)

    def rec_status_text(self, rec):
        icon = "⏹" if rec.finished else "🔴"
        lines = [f"{icon} @{rec.user}" + (" (terminó)" if rec.finished else " en vivo")]
        lines.append(f"⏱ Grabado: {fmt_dur(rec.recorded_seconds())}")
        at = rec.airtime()
        if at:
            lines.append(f"📺 El live lleva: {fmt_dur(at)}")
        if rec.quality:
            opts = ", ".join(rec.qual_options)
            lines.append(f"🎞 Calidad: {rec.quality} (disponibles: {opts}; manifiestos probados: {rec.n_manifests})")
        up = f" · 📤 subiendo {rec.uploading}" if rec.uploading else ""
        lines.append(f"📦 Videos subidos a Telegram: {rec.sent}{up}")
        lines.append(f"🔎 Detectado por: {rec.via or '?'} · método: {rec.method or 'iniciando…'}")
        return "\n".join(lines)

    async def _status_loop(self, rec):
        while not rec.finished:
            await asyncio.sleep(30)
            if rec.finished or not rec.status_msg:
                break
            try:
                await rec.status_msg.edit(self.rec_status_text(rec), parse_mode=None)
            except Exception as e:
                if "not modified" not in str(e).lower():
                    log.debug("No pude actualizar el cronómetro: %s", e)

    # ---------- descargar historias, publicaciones y reels por enlace ----------
    async def upload_photo(self, user, path, caption):
        async with self.upload_sem:
            for attempt in range(1, 4):
                try:
                    tid = await self.ensure_topic(user)
                    sent = await self.client.send_file(
                        self.chat, path, caption=caption, reply_to=tid, parse_mode=None
                    )
                    self.last_sent = sent
                    return True
                except Exception as e:
                    log.warning("Subida de foto falló (intento %d): %s", attempt, e)
                    if "TOPIC" in str(e).upper():
                        self.state.data["topics"].pop(user, None)
                    await asyncio.sleep(3 * attempt)
            return False

    def message_link(self, user, msg):
        cid = str(CFG.chat_id)
        cid = cid[4:] if cid.startswith("-100") else cid.lstrip("-")
        tid = self.state.data["topics"].get(user)
        if tid:
            return f"https://t.me/c/{cid}/{tid}/{msg.id}"
        return f"https://t.me/c/{cid}/{msg.id}"

    async def deliver_files(self, files):
        sent, msgs = 0, []
        for f in files:
            path, user = f["path"], f["user"].lower()
            ext = os.path.splitext(path)[1].lower()
            now = datetime.now(CFG.tz)
            tag_user = re.sub(r"\W+", "_", user)
            caption = (
                f"📥 @{user} · {f['type']}\n"
                f"📅 {now.strftime('%Y-%m-%d · %H:%M')} ({CFG.tz.key})\n"
                f"#{tag_user} #{now.strftime('%Y_%m_%d')}"
            )
            thumb = None
            if ext in (".mp4", ".mov", ".mkv", ".webm"):
                dur, w, h = await probe_video(path)
                thumb = path + ".jpg"
                await run_cmd("ffmpeg", "-v", "error", "-y", "-ss", "0.5", "-i", path,
                              "-frames:v", "1", "-vf", "scale=320:-1", thumb)
                if not os.path.exists(thumb):
                    thumb = None
                meta = {"kind": f["type"], "when": now.isoformat(), "size": os.path.getsize(path)}
                ok = await self.upload_video(user, path, caption, dur, w, h, thumb, meta)
            else:
                ok = await self.upload_photo(user, path, caption)
            if ok:
                sent += 1
                if self.last_sent is not None:
                    msgs.append((user, self.last_sent))
            for p in (path, thumb):
                if p and os.path.exists(p):
                    os.remove(p)
        return sent, msgs

    async def download_link(self, link):
        """Descarga historias, publicaciones o reels y los manda a este chat. Devuelve el texto de respuesta."""
        workdir = os.path.join(CFG.rec_dir, "_descargas", datetime.now().strftime("%H%M%S%f"))
        try:
            files = await asyncio.to_thread(self.ig.fetch_content, link, workdir)
        except Exception as e:
            shutil.rmtree(workdir, ignore_errors=True)
            return "❌ No pude descargar: " + html.escape(str(e)[:200])
        if not files:
            shutil.rmtree(workdir, ignore_errors=True)
            return "⚪ No encontré nada que descargar (¿cuenta privada o sin historias activas?)."
        n, _ = await self.deliver_files(files)
        shutil.rmtree(workdir, ignore_errors=True)
        if n == 0:
            return "❌ Descargué el contenido, pero no pude enviarlo."
        return f"✅ Listo: {n} de {len(files)} archivo(s) de @{html.escape(files[0]['user'])} enviados aquí abajo."

    async def handle_link(self, text):
        """Lo que se hace al recibir un enlace o una cuenta. Devuelve (texto, botones o None)."""
        link = classify_link(text)
        kind = link["kind"]
        if kind == "live":
            return await self.record_target(text), None
        if kind == "none":
            return "❌ No entendí el enlace. Envía un enlace de Instagram (cuenta, live, historia, publicación o reel).", None
        if not self.ig.ok:
            return "❌ Primero inicia sesión en Instagram (menú → 🔑 Sesión IG).", None
        if kind == "highlight":
            return "ℹ️ Los destacados todavía no los descargo. Pega el enlace de una historia o una publicación.", None
        if kind == "profile" and link["user"]:
            return self.account_menu(link["user"])
        return await self.download_link(link), None

    # ---------- biblioteca de videos y menú por cuenta ----------
    @staticmethod
    def _num(n):
        try:
            return f"{int(n):,}".replace(",", ".")
        except Exception:
            return "?"

    def _when(self, iso):
        try:
            return datetime.fromisoformat(iso).astimezone(CFG.tz).strftime("%d/%m/%Y %H:%M")
        except Exception:
            return "?"

    async def library_add(self, user, sent, dur, meta):
        lib = self.state.data.setdefault("library", {})
        lib.setdefault(user.lower(), []).append({
            "id": sent.id, "when": meta.get("when"), "kind": meta.get("kind", "live"),
            "dur": int(dur or 0), "size": int(meta.get("size") or 0), "part": meta.get("part"),
        })
        await asyncio.to_thread(self.state.save)

    def account_menu(self, user):
        n = len(self.state.data.get("library", {}).get(user, []))
        text = (f"👤 <b>@{html.escape(user)}</b>\n"
                f"📼 Videos guardados aquí: <b>{n}</b>\n\n¿Qué quieres hacer?")
        B = Button.inline
        return text, [
            [B("🔴 Grabar", f"accrec:{user}".encode()), B("📼 Videos grabados", f"acclist:{user}:0".encode())],
            [B("ℹ️ Información", f"accinfo:{user}".encode()), B("📥 Historias", f"accstories:{user}".encode())],
            [B("⬅️ Menú", b"menu")],
        ]

    async def account_info_text(self, user, force=False):
        cached = self.acc_cache.get(user)
        if cached and not force and time.time() - cached[0] < 600:
            info = cached[1]
        else:
            if not self.ig.ok:
                return "❌ Primero inicia sesión en Instagram (🔑 Sesión IG)."
            try:
                info = await asyncio.to_thread(self.ig.account_details, user)
            except Exception as e:
                return "❌ No pude leer la cuenta: " + html.escape(str(e)[:200])
            self.acc_cache[user] = (time.time(), info)
        e = html.escape
        lines = [f"👤 <b>@{e(info['user'])}</b>" + (" ✔️" if info["verified"] else "")]
        if info["name"]:
            lines.append(f"📛 {e(info['name'])}")
        lines.append("━━━━━━━━━━━━━━")
        lines += [
            f"👥 Seguidores: <b>{self._num(info['followers'])}</b>",
            f"➡️ Siguiendo: <b>{self._num(info['following'])}</b>",
            f"🖼 Publicaciones: <b>{self._num(info['posts'])}</b>",
            f"🔒 Cuenta: {'privada' if info['private'] else 'pública'}",
        ]
        if info["category"]:
            lines.append(f"🏷 Categoría: {e(info['category'])}")
        if info["url"]:
            lines.append(f"🔗 {e(info['url'])}")
        if info["bio"]:
            lines.append(f"📝 {e(info['bio'][:300])}")
        lines.append("━━━━━━━━━━━━━━")
        return "\n".join(lines)

    def library_screen(self, user, page):
        B = Button.inline
        back = [B("⬅️ Cuenta", f"acc:{user}".encode())]
        lib = list(reversed(self.state.data.get("library", {}).get(user, [])))
        if not lib:
            return f"📼 <b>@{html.escape(user)}</b>\n\nTodavía no hay videos guardados de esta cuenta.", [back]
        PAGE = 6
        pages = max(1, math.ceil(len(lib) / PAGE))
        page = min(max(page, 0), pages - 1)
        total = sum(x.get("size", 0) for x in lib)
        rows = []
        for x in lib[page * PAGE:(page + 1) * PAGE]:
            icon = "🔴" if x.get("kind") == "live" else "📥"
            part = f" · p{x['part']}" if x.get("part") else ""
            label = f"{icon} {self._when(x.get('when'))} · {fmt_dur(x.get('dur', 0))} · {fmt_size(x.get('size', 0))}{part}"
            rows.append([B(label, f"play:{x['id']}".encode())])
        nav = []
        if page > 0:
            nav.append(B("◀️", f"acclist:{user}:{page - 1}".encode()))
        nav.append(B(f"{page + 1}/{pages}", b"noop"))
        if page < pages - 1:
            nav.append(B("▶️", f"acclist:{user}:{page + 1}".encode()))
        rows += [nav, back]
        return (f"📼 <b>@{html.escape(user)}</b>\n{len(lib)} videos · {fmt_size(total)}\n"
                "Toca uno para recibirlo aquí (más nuevos primero)."), rows

    # ---------- diseño: menú con botones ----------
    HELP = (
        "❓ <b>Ayuda</b>\n\n"
        "• <b>Automático:</b> graba solo los lives de las cuentas que sigues.\n"
        "• <b>Por enlace o cuenta:</b> pega el enlace o @usuario de una cuenta y te pregunto qué hacer (grabar, ver sus videos guardados con fecha y hora, información). Un enlace de live lo graba; de historia, publicación o reel lo descarga.\n"
        "• Mientras graba verás un cronómetro que se actualiza solo, con el tiempo grabado y lo que lleva el live.\n"
        "• <b>Perfiles a grabar:</b> marca tus cuentas favoritas de la lista de las que sigues; el bot las revisa una por una, además de la detección general.\n"
        "• Los videos llegan a este chat. En 📚 Biblioteca los ves por cuenta, con fecha y hora.\n\n"
        "<b>Comandos:</b>\n"
        "/menu · /estado · /siguiendo · /diag · /probar · /grabar enlace\n"
        "/login usuario clave [2FA] · /sessionid VALOR\n"
        "/solo u1 u2 · /todos\n"
        "/lista"
    )

    @staticmethod
    def _back():
        return [Button.inline("⬅️ Menú", b"menu")]

    def menu_text(self):
        d = self.state.data
        ig = ("@" + html.escape(str(self.ig.user))) if self.ig.ok else "❌ sin sesión"
        modo = f"solo {len(d['only'])} cuenta(s)" if d["only"] else "todas las que sigues"
        left = max(0, CFG.max_runtime - (time.time() - self.t0))
        return (
            "🎥 <b>Grabador de lives de Instagram</b>\n\n"
            "🟢 Operativo\n"
            f"👤 Instagram: {ig}\n"
            f"{self.following_line()}\n"
            f"🔴 Grabando ahora: {len(self.active)}\n"
            f"📋 Perfiles marcados: {len(d['picks'])}\n"
            f"🎯 Modo: {modo}\n"
            f"⏱ Consulta cada {CFG.poll} segundos\n"
            f"⏳ Turno actual termina en {fmt_dur(left)}\n\n"
            "Selecciona una opción:"
        )

    def menu_buttons(self):
        B = Button.inline
        return [
            [B("📊 Estado", b"estado"), B("🔴 En vivo ahora", b"vivo")],
            [B("🔗 Enlace o cuenta", b"grabar"), B("📚 Biblioteca", b"lib")],
            [B("📋 Perfiles a grabar", b"perfiles"), B("🔑 Sesión IG", b"sesion")],
            [B("🩺 Diagnóstico", b"diag"), B("🔬 Probar detección", b"probe")],
            [B("❓ Ayuda", b"ayuda")],
        ]

    def estado_text(self):
        ig = ("@" + html.escape(str(self.ig.user))) if self.ig.ok else "❌ sin sesión"
        lines = [f"📊 <b>Estado</b>\n\n👤 Instagram: {ig}\n{self.following_line()}"]
        if self.active:
            lines.append(f"🔴 Grabando ahora ({len(self.active)}):")
            for r in self.active.values():
                lines.append("  • " + self.rec_line(r))
        else:
            lines.append("⚪ No hay ningún live grabándose ahora.")
        left = max(0, CFG.max_runtime - (time.time() - self.t0))
        lines.append(f"⏳ El turno actual termina en {fmt_dur(left)} (se relanza solo)")
        return "\n".join(lines)

    def diag_text(self):
        i = self.ig.last_info
        if not i:
            return "🩺 <b>Diagnóstico</b>\n\nAún no he consultado Instagram."
        lines = [f"🩺 <b>Diagnóstico</b>\n\nÚltima consulta hace {int(time.time() - i['time'])} s · "
                 f"sesión: {'OK' if self.ig.ok else 'caída'}"]
        lines += [f"• {html.escape(k)}: {html.escape(str(v))}" for k, v in i["endpoints"].items()]
        lines += [f"• perfil {html.escape(w)}" for w in i.get("picks", [])]
        lines.append(f"Lives detectados: {i['total']}")
        return "\n".join(lines)

    async def screen(self, key, event):
        """Devuelve (texto, botones) de cada pantalla del menú."""
        B = Button.inline
        d = self.state.data
        back = self._back()
        if key == "menu":
            await self.refresh_following()
            return self.menu_text(), self.menu_buttons()
        if key == "estado":
            await self.refresh_following()
            return self.estado_text(), [[B("🔄 Actualizar", b"estado")], back]
        if key == "vivo":
            if not self.active:
                return "⚪ <b>Nadie se está grabando ahora.</b>", [[B("🔄 Actualizar", b"vivo")], back]
            rows = []
            lines = ["🔴 <b>Grabando ahora</b>\n"]
            for bid, r in self.active.items():
                lines.append("• " + self.rec_line(r))
                rows.append([B(f"⏹ Detener @{r.user}", f"stop:{bid}".encode())])
            return "\n".join(lines), rows + [[B("🔄 Actualizar", b"vivo")], back]
        if key == "grabar":
            self.pending = "grabar"
            return (
                "🔗 <b>Enlace o cuenta</b>\n\n"
                "Envíame:\n"
                "• El <b>enlace o @usuario de una cuenta</b> → te muestro qué puedo hacer: grabar su live, "
                "ver los videos guardados con fecha y hora, o ver su información.\n"
                "• Un <b>enlace de live</b> → lo grabo (si está en vivo ahora).\n"
                "• Un <b>enlace de historia, publicación o reel</b> → lo descargo y te lo mando aquí.\n\n"
                "Ejemplos:\n<code>https://www.instagram.com/usuario/</code>\n<code>@usuario</code>"
            ), [back]
        if key == "lib":
            lib = d.get("library", {})
            if not lib:
                return "📚 <b>Biblioteca</b>\n\nTodavía no hay videos guardados.", [back]
            rows = []
            ordered = sorted(lib.items(), key=lambda kv: max((x.get("when") or "") for x in kv[1]), reverse=True)
            for u, items in ordered[:30]:
                total = sum(x.get("size", 0) for x in items)
                rows.append([B(f"👤 @{u} · {len(items)} · {fmt_size(total)}", f"acc:{u}".encode())])
            return "📚 <b>Biblioteca</b>\n\nElige una cuenta:", rows + [back]
        if key.startswith("acc:"):
            return self.account_menu(key[4:])
        if key.startswith("accinfo:") or key.startswith("accrefresh:"):
            u = key.split(":", 1)[1]
            text = await self.account_info_text(u, force=key.startswith("accrefresh:"))
            return text, [[B("🔄 Actualizar", f"accrefresh:{u}".encode())], [B("⬅️ Cuenta", f"acc:{u}".encode())]]
        if key.startswith("acclist:"):
            _, u, pg = key.split(":", 2)
            return self.library_screen(u, int(pg or 0))
        if key.startswith("accrec:"):
            u = key.split(":", 1)[1]
            return await self.record_target("@" + u), [[B("⬅️ Cuenta", f"acc:{u}".encode())]]
        if key.startswith("accstories:"):
            u = key.split(":", 1)[1]
            if not self.ig.ok:
                return "❌ Primero inicia sesión en Instagram (🔑 Sesión IG).", [[B("⬅️ Cuenta", f"acc:{u}".encode())]]
            text = await self.download_link({"kind": "stories_user", "user": u, "url": None})
            return text, [[B("⬅️ Cuenta", f"acc:{u}".encode())]]
        if key.startswith("perfiles"):
            if not self.ig.ok:
                return "❌ Primero inicia sesión en Instagram (🔑 Sesión IG).", [back]
            names = d.get("following_names") or []
            if not names:
                try:
                    await asyncio.to_thread(self.ig.fetch_following_list)
                except Exception as e:
                    return "❌ No pude leer la lista de cuentas que sigues: " + html.escape(str(e)[:200]), [back]
                names = d.get("following_names") or []
            if not names:
                return "⚪ No encontré cuentas en tu lista de seguidos.", [back]
            PAGE = 8
            pages = max(1, math.ceil(len(names) / PAGE))
            try:
                page = int(key.split(":")[1]) if ":" in key else 0
            except ValueError:
                page = 0
            page = min(max(page, 0), pages - 1)
            picks = set(d["picks"])
            rows = [
                [B(("✅ " if u in picks else "⬜ ") + "@" + u, f"pick:{u}:{page}".encode())]
                for u in names[page * PAGE:(page + 1) * PAGE]
            ]
            nav = []
            if page > 0:
                nav.append(B("◀️", f"perfiles:{page - 1}".encode()))
            nav.append(B(f"{page + 1}/{pages}", b"noop"))
            if page < pages - 1:
                nav.append(B("▶️", f"perfiles:{page + 1}".encode()))
            rows.append(nav)
            rows.append([B("🔄 Recargar lista", b"perfiles_reload"), back[0]])
            return (
                "📋 <b>Perfiles a grabar</b>\n\n"
                "Toca una cuenta para marcarla ✅. Las marcadas se revisan una por una en cada ronda. "
                "Las demás que sigues también se graban por la detección general.\n\n"
                f"Marcadas: {len(picks)} · Sigues a {len(names)}"
            ), rows
        if key == "solo":
            self.pending = "solo"
            lst = ", ".join("@" + html.escape(w) for w in d["only"]) or "todas las que sigues"
            return (
                "🎯 <b>Solo estas cuentas</b>\n\n"
                f"Ahora grabo: {lst}\n\nEnvíame los @usuarios que quieres grabar (separados por espacio)."
            ), [[B("🌐 Grabar a todas", b"todos")], back]
        if key == "todos":
            d["only"] = []
            await asyncio.to_thread(self.state.save)
            return await self.screen("solo", event)
        if key == "probe":
            if not self.ig.ok:
                return "❌ Primero inicia sesión en Instagram (🔑 Sesión IG).", [back]
            try:
                lines = await asyncio.to_thread(self.ig.deep_probe, list(d.get("picks", [])))
            except Exception as e:
                return "❌ La prueba falló: " + html.escape(str(e)[:200]), [back]
            body = "\n".join(html.escape(x) for x in lines)
            tip = "" if d.get("picks") else "\n\nℹ️ Marca algunas cuentas en 📋 Perfiles a grabar para probar también la ruta por perfil."
            return ("🔬 <b>Prueba de detección</b>\n\n" + body + tip)[:3900], [[B("🔄 Repetir", b"probe")], back]
        if key == "diag":
            return self.diag_text(), [[B("🔄 Actualizar", b"diag")], back]
        if key == "sesion":
            ig = ("@" + html.escape(str(self.ig.user))) if self.ig.ok else "❌ sin sesión"
            return (
                f"🔑 <b>Sesión de Instagram</b>\n\nAhora: {ig}\n\nElige cómo iniciar sesión:"
            ), [[B("🍪 Con sessionid", b"sesion_sid")], [B("🔑 Usuario y clave", b"sesion_login")], back]
        if key == "sesion_sid":
            if not event.is_private:
                return "Usa esto solo en el chat privado conmigo.", [back]
            self.pending = "sessionid"
            return "🍪 Pega aquí el valor del <b>sessionid</b>. Borraré tu mensaje al instante.", [back]
        if key == "sesion_login":
            if not event.is_private:
                return "Usa esto solo en el chat privado conmigo.", [back]
            self.pending = "login"
            return ("🔑 Envía: <code>usuario clave</code>\nSi tienes 2FA: <code>usuario clave 123456</code>\n"
                    "Borraré tu mensaje al instante."), [back]
        if key == "ayuda":
            return self.HELP, [back]
        return self.menu_text(), self.menu_buttons()

    async def on_callback(self, event):
        data = event.data.decode()
        try:
            await event.answer()
        except Exception:
            pass
        self.pending = None
        if data == "noop":
            return
        if data.startswith("play:"):
            mid = int(data[5:])
            try:
                await self.client.forward_messages(CFG.admin_id, [mid], from_peer=CFG.admin_id)
            except Exception as e:
                log.warning("No pude reenviar el video %s: %s", mid, e)
                for items in self.state.data.get("library", {}).values():
                    items[:] = [x for x in items if x.get("id") != mid]
                await asyncio.to_thread(self.state.save)
                await self.notify("⚠️ No pude enviarte ese video (¿lo borraste del chat?). Lo quité de la lista.")
            return
        if data.startswith("pick:"):
            _, u, pg = data.split(":", 2)
            picks = self.state.data.setdefault("picks", [])
            if u in picks:
                picks.remove(u)
            else:
                picks.append(u)
            await asyncio.to_thread(self.state.save)
            data = f"perfiles:{pg}"
        elif data == "perfiles_reload":
            self.state.data["following_names"] = []
            data = "perfiles:0"
        if data.startswith("stop:"):
            rec = self.active.get(data[5:])
            if rec:
                rec.request_stop()
            data = "vivo"
        text, buttons = await self.screen(data, event)
        try:
            await event.edit(text, buttons=buttons)
        except Exception as e:
            if "not modified" not in str(e).lower():
                log.warning("No pude editar el menú: %s", e)

    # ---------- mensajes y comandos ----------
    async def _try_delete(self, event):
        try:
            await event.delete()   # borra tu mensaje con la clave
        except Exception:
            pass

    @staticmethod
    def _names(text):
        out = []
        for tok in text.replace(",", " ").split():
            u, _ = parse_target(tok)
            if u and u not in out:
                out.append(u)
        return out

    async def on_message(self, event):
        text = (event.raw_text or "").strip()
        if not text:
            return
        if text.startswith("/"):
            return await self.on_command(event, text)
        pend, self.pending = self.pending, None
        d = self.state.data
        back = [self._back()]
        if pend in ("sessionid", "login") and not event.is_private:
            return
        if pend == "grabar" or (pend is None and (LINK_RE.search(text) or re.fullmatch(r"@[A-Za-z0-9._]{1,30}", text))):
            msg = await event.reply("⏳ Trabajando en tu enlace…")
            out, btns = await self.handle_link(text)
            await msg.edit(out, buttons=btns or back)
        elif pend == "solo":
            d["only"] = self._names(text)
            await asyncio.to_thread(self.state.save)
            await event.reply("🎯 Solo grabaré: " + ", ".join("@" + html.escape(w) for w in d["only"]), buttons=back)
        elif pend == "sessionid":
            msg = await event.reply("⏳ Verificando sesión…")
            ok, txt = await asyncio.to_thread(self.ig.login_sessionid, text.split()[0])
            await self._try_delete(event)
            if ok:
                self.session_alert_sent = False
            await msg.edit(html.escape(txt), buttons=back)
        elif pend == "login":
            parts = text.split()
            if len(parts) < 2:
                return await event.reply("Formato: usuario clave [codigo2FA]", buttons=back)
            msg = await event.reply("⏳ Iniciando sesión…")
            ok, txt = await asyncio.to_thread(
                self.ig.login, parts[0].lstrip("@"), parts[1], parts[2] if len(parts) > 2 else ""
            )
            await self._try_delete(event)
            if ok:
                self.session_alert_sent = False
            await msg.edit(html.escape(txt), buttons=back)
        else:
            await event.reply(self.menu_text(), buttons=self.menu_buttons())

    async def on_command(self, event, text):
        cmd, *args = text.split()
        cmd = cmd.split("@")[0].lower()
        reply = event.reply
        d = self.state.data
        back = [self._back()]
        self.pending = None

        if cmd in ("/start", "/menu"):
            await self.refresh_following()
            await reply(self.menu_text(), buttons=self.menu_buttons())
        elif cmd in ("/ayuda", "/help"):
            await reply(self.HELP, buttons=back)
        elif cmd == "/grabar":
            if not args:
                return await reply("Uso: /grabar enlace_del_live  (o /grabar @usuario)")
            msg = await reply("⏳ Trabajando en tu enlace…")
            out, btns = await self.handle_link(" ".join(args))
            await msg.edit(out, buttons=btns or back)
        elif cmd == "/login":
            if not event.is_private:
                return await reply("Por seguridad usa /login solo en chat privado conmigo.")
            if len(args) < 2:
                return await reply("Uso: /login usuario clave [codigo2FA]")
            msg = await reply("⏳ Iniciando sesión…")
            ok, txt = await asyncio.to_thread(
                self.ig.login, args[0].lstrip("@"), args[1], args[2] if len(args) > 2 else ""
            )
            await self._try_delete(event)
            if ok:
                self.session_alert_sent = False
            await msg.edit(html.escape(txt), buttons=back)
        elif cmd == "/sessionid":
            if not event.is_private:
                return await reply("Usa /sessionid solo en chat privado conmigo.")
            if not args:
                return await reply("Uso: /sessionid VALOR_DE_LA_COOKIE")
            msg = await reply("⏳ Verificando sesión…")
            ok, txt = await asyncio.to_thread(self.ig.login_sessionid, args[0])
            await self._try_delete(event)
            if ok:
                self.session_alert_sent = False
            await msg.edit(html.escape(txt), buttons=back)
        elif cmd in ("/estado", "/siguiendo"):
            await self.refresh_following(force=True)
            await reply(self.estado_text(), buttons=back)
        elif cmd == "/probar":
            text, btns = await self.screen("probe", event)
            await reply(text, buttons=btns)
        elif cmd == "/diag":
            await reply(self.diag_text(), buttons=back)
        elif cmd == "/solo" and args:
            d["only"] = self._names(" ".join(args))
            await asyncio.to_thread(self.state.save)
            await reply("🎯 Solo grabaré: " + ", ".join("@" + html.escape(w) for w in d["only"]), buttons=back)
        elif cmd == "/todos":
            d["only"] = []
            await asyncio.to_thread(self.state.save)
            await reply("🌐 Grabaré a todas las cuentas que sigues.", buttons=back)
        elif cmd == "/lista":
            await reply(
                f"🎯 Solo: {html.escape(', '.join(d['only']) or '— (todas las que sigues)')}",
                buttons=back,
            )
        else:
            await reply("Comando no reconocido. Usa /menu", buttons=back)

    # ---------- bucle de búsqueda ----------
    async def sleep(self, seconds):
        try:
            await asyncio.wait_for(self.stop_event.wait(), seconds)
        except asyncio.TimeoutError:
            pass

    async def _run_rec(self, rec):
        try:
            rec.status_msg = await self.client.send_message(
                CFG.admin_id, self.rec_status_text(rec), parse_mode=None
            )
            rec.status_task = asyncio.create_task(self._status_loop(rec))
        except Exception as e:
            log.warning("No pude enviar el cronómetro: %s", e)
        try:
            await rec.run()
        except Exception as e:
            rec.fail_reason = f"error interno: {str(e)[:200]}"
            log.exception("Error grabando @%s: %s", rec.user, e)
        finally:
            rec.finished = True
            self.active.pop(rec.id, None)
            if rec.status_task:
                rec.status_task.cancel()
            if rec.status_msg:
                try:
                    await rec.status_msg.edit(self.rec_status_text(rec), parse_mode=None)
                except Exception:
                    pass
            ran = time.time() - rec.t0
            if ran < 90:
                self.cooldown[rec.id] = time.time() + 90
            if rec.sent:
                await self.notify(f"✅ Live de @{rec.user} guardado en Telegram ({rec.sent} parte/s).")
            else:
                self.fail_count[rec.id] = self.fail_count.get(rec.id, 0) + 1
                if rec.id not in self.fail_notified:
                    self.fail_notified.add(rec.id)
                    await self.notify(rec.failure_text(ran))

    async def handle_lives(self, lives):
        now = time.time()
        current = {b["id"]: b for b in lives}
        for bid, b in current.items():
            rec = self.active.get(bid)
            if rec:
                rec.missing = 0
                continue
            if not self.allowed(b["username"]) or self.cooldown.get(bid, 0) > now:
                continue
            if self.fail_count.get(bid, 0) >= 3:
                continue   # falló 3 veces: no insisto con este live
            rec = Recording(self, b)
            self.active[bid] = rec
            rec.task = asyncio.create_task(self._run_rec(rec))
            self.notified.add(bid)
        for bid, rec in list(self.active.items()):
            if bid in current:
                continue
            if rec.manual:
                alive = await asyncio.to_thread(self.ig.broadcast_alive, bid)
                if alive is False:
                    rec.missing += 1
                    if rec.missing >= 2:
                        rec.request_stop()
                elif alive:
                    rec.missing = 0
                continue
            rec.missing += 1
            if rec.missing >= 3:
                rec.request_stop()

    async def poll_loop(self):
        errors = 0
        last_save = time.time()
        last_follow = 0.0
        while not self.stop_event.is_set() and time.time() - self.t0 < CFG.max_runtime:
            wait = CFG.poll + random.uniform(0, 10)
            if not self.ig.ok:
                await self.sleep(20)
                continue
            try:
                lives = await asyncio.to_thread(self.ig.live_broadcasts)
                errors = 0
                log.info("Consulta IG: %d live(s) detectado(s) | %s", len(lives), (self.ig.last_info or {}).get("endpoints"))
                await self.handle_lives(lives)
                for u in (self.ig.last_info or {}).get("unparsed", []):
                    key = u.split(":")[0]
                    if key not in self.unparsed_seen:
                        self.unparsed_seen.add(key)
                        await self.notify(
                            "⚠️ Detecté un live pero no pude leer su enlace de video. "
                            "Mándale este mensaje a Claude para arreglarlo:\n" + u[:700]
                        )
                if time.time() - last_follow > 1800:
                    last_follow = time.time()
                    await self.refresh_following(force=True)
                if time.time() - last_save > 1800:
                    last_save = time.time()
                    await asyncio.to_thread(self.ig.persist)
            except Exception as e:
                msg = str(e).lower()
                if isinstance(e, LoginRequired) or any(
                    k in msg for k in ("login_required", "checkpoint", "challenge_required")
                ):
                    self.ig.ok = False
                    if not self.session_alert_sent:
                        self.session_alert_sent = True
                        await self.notify(
                            "⚠️ La sesión de Instagram se cayó. Envíame /sessionid o /login para reconectar."
                        )
                else:
                    errors += 1
                    log.warning("Error buscando lives (%d): %s", errors, e)
                    wait = min(600, 30 * errors)
                    if errors == 6:
                        await self.notify(f"⚠️ Instagram está dando errores seguidos: {str(e)[:200]}")
            await self.sleep(wait)

    # ---------- arranque ----------
    async def run(self):
        await self.client.start(bot_token=CFG.bot_token)
        self.state.data["tg_session"] = self.client.session.save()
        await asyncio.to_thread(self.state.save)
        self.chat = CFG.admin_id

        self.client.add_event_handler(
            self.on_message, events.NewMessage(incoming=True, from_users=CFG.admin_id)
        )
        self.client.add_event_handler(
            self.on_callback, events.CallbackQuery(func=lambda e: e.sender_id == CFG.admin_id)
        )
        loop = asyncio.get_running_loop()
        for sig in (signal.SIGTERM, signal.SIGINT):
            try:
                loop.add_signal_handler(sig, self.stop_event.set)
            except NotImplementedError:
                pass

        if not self.ig.ok:
            try:
                await self.client.send_message(
                    CFG.admin_id,
                    "👋 Bot activo, pero falta iniciar sesión en Instagram.\n\n" + self.menu_text(),
                    buttons=self.menu_buttons(),
                )
            except Exception as e:
                log.warning("No pude enviar el menú: %s", e)
        log.info("Bot listo. Esperando lives…")

        await self.poll_loop()

        log.info("Cerrando turno: finalizando grabaciones…")
        for rec in self.active.values():
            rec.request_stop()
        tasks = [r.task for r in self.active.values() if r.task]
        if tasks:
            await asyncio.wait(tasks, timeout=900)
        if self.ig.cl:
            await asyncio.to_thread(self.ig.persist)
        await asyncio.to_thread(self.state.save)
        await self.client.disconnect()


def main():
    global CFG
    CFG = load_config()
    os.makedirs(CFG.rec_dir, exist_ok=True)
    if not shutil.which("ffmpeg"):
        sys.exit("❌ ffmpeg no está instalado")
    asyncio.run(App().run())


if __name__ == "__main__":
    main()
