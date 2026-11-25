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
from collections import deque
from datetime import datetime, timedelta
from types import SimpleNamespace
from zoneinfo import ZoneInfo

from cryptography.fernet import Fernet, InvalidToken
from telethon import Button, TelegramClient, events
from telethon.sessions import StringSession
from telethon.tl.functions.channels import GetChannelsRequest
from telethon.tl.types import DocumentAttributeVideo, InputChannel, InputPeerChannel

from instagrapi import Client as IGClient
from instagrapi.exceptions import BadPassword, ChallengeRequired, LoginRequired, TwoFactorRequired

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
        chat_id=int(_env("TG_CHAT_ID", required=True)),   # grupo donde se suben los videos
        admin_id=int(_env("ADMIN_ID", required=True)),    # tu ID: solo tú puedes mandar comandos
        state_key=_env("STATE_KEY", required=True),       # clave para cifrar la sesión guardada
        ig_proxy=_env("IG_PROXY", ""),                    # opcional: http://user:pass@host:port
        tz=ZoneInfo(_env("TZ_NAME", "America/Lima")),     # tu zona horaria
        pick_batch=int(_env("PICK_BATCH", "10")),          # perfiles marcados revisados por ronda
        poll=int(_env("POLL_SECONDS", "45")),             # cada cuántos seg. busca lives nuevos
        max_runtime=int(_env("MAX_RUNTIME_MIN", "345")) * 60,  # turno de GitHub (máx 6h)
        segment=int(_env("SEGMENT_SECONDS", "2400")),     # corta partes de 40 min (límite Telegram 2GB)
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
            "topics": {},          # usuario -> id del tema en el grupo
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
        cl = self.cl
        if name == "tray_get":
            return cl.private_request("feed/reels_tray/")
        return cl.private_request(
            "feed/get_reels_tray_feed/",
            data={
                "reason": "pull_to_refresh",
                "timezone_offset": "-18000",
                "tray_session_id": cl.generate_uuid(),
                "request_id": cl.generate_uuid(),
                "page_size": 50,
                "_uuid": cl.uuid,
            },
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
            res = self._fetch_tray("tray_get")
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
                info["endpoints"]["bandeja"] = f"ok | lives={len(raw)} validos={n_ok} | claves: {keys}"
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
                    res = self.cl.private_request(f"feed/user/{pk}/story/")
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
        res = self._fetch_tray("tray_get")
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
                res = cl.private_request(f"feed/user/{pk}/story/")
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
        ]
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
        v, a, self.probe_err = await pick_best_streams(url)
        maps = []
        if v is not None:
            maps += ["-map", f"0:{v}"]
        if a is not None:
            maps += ["-map", f"0:{a}"]
        log.info("Grabando @%s (video stream %s, audio stream %s)", self.user, v, a)

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
        shutil.rmtree(self.dir, ignore_errors=True)

    async def _upload_ready(self, final):
        files = sorted(glob.glob(os.path.join(self.dir, "part_*.mkv")))
        ready = files if final else files[:-1]   # la última parte aún se está escribiendo
        for f in ready:
            await self._upload(f)

    async def _upload(self, mkv):
        mp4 = mkv[:-4] + ".mp4"
        rc, _, err = await run_cmd(
            "ffmpeg", "-v", "error", "-y", "-i", mkv, "-c", "copy", "-movflags", "+faststart", mp4
        )
        if rc != 0 or not os.path.exists(mp4):
            log.warning("No pude convertir %s: %s", mkv, err[-200:])
            os.rename(mkv, mkv + ".bad")
            return
        os.remove(mkv)
        dur, w, h = await probe_video(mp4)
        if dur < 3 or os.path.getsize(mp4) < 150_000:
            self.dropped.append(f"{dur:.1f}s, {fmt_size(os.path.getsize(mp4))}")
            os.remove(mp4)
            return

        part_start = self.start + timedelta(seconds=self.cum)
        self.cum += dur
        self.part += 1

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
            extra = f" · parte {self.part}" + (f".{i + 1}" if len(pieces) > 1 else "")
            caption = (
                f"🔴 @{self.user}\n"
                f"📅 {part_start.strftime('%Y-%m-%d · %H:%M')} ({CFG.tz.key})\n"
                f"⏱ {fmt_dur(d)} · 📦 {fmt_size(os.path.getsize(p))} · 📺 {pw}x{ph}{extra}\n"
                f"#{tag_user} #{tag_date}"
            )
            ok = await self.app.upload_video(self.user, p, caption, d, pw, ph, thumb)
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
        self.use_topics = True
        self.session_alert_sent = False
        self.pending = None       # lo que espera el menú (enlace, usuarios…)
        self.unparsed_seen = set()
        self.fail_count = {}
        self.fail_notified = set()
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
            topics = self.state.data["topics"]
            if user in topics:
                return topics[user]
            if not self.use_topics:
                return None
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

    async def upload_video(self, user, path, caption, dur, w, h, thumb):
        async with self.upload_sem:
            for attempt in range(1, 4):
                try:
                    tid = await self.ensure_topic(user)
                    await self.client.send_file(
                        self.chat, path, caption=caption, thumb=thumb, reply_to=tid,
                        attributes=[DocumentAttributeVideo(
                            duration=int(dur), w=w, h=h, supports_streaming=True)],
                        force_document=False, part_size_kb=512, parse_mode=None,
                    )
                    return True
                except Exception as e:
                    log.warning("Subida falló (intento %d): %s", attempt, e)
                    if "TOPIC" in str(e).upper():
                        self.state.data["topics"].pop(user, None)   # tema borrado: se recrea
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
                "El video llega al grupo cuando termine el live. Si algo falla, te aviso aquí.")

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

    # ---------- diseño: menú con botones ----------
    HELP = (
        "❓ <b>Ayuda</b>\n\n"
        "• <b>Automático:</b> graba solo los lives de las cuentas que sigues.\n"
        "• <b>Por enlace:</b> pega un enlace de un live (o el @usuario) y lo grabo.\n"
        "• <b>Perfiles a grabar:</b> marca tus cuentas favoritas de la lista de las que sigues; el bot las revisa una por una, además de la detección general.\n"
        "• Los videos llegan al grupo, un tema por usuario, con fecha y hora.\n\n"
        "<b>Comandos:</b>\n"
        "/menu · /estado · /siguiendo · /diag · /grabar enlace\n"
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
            [B("🔗 Grabar enlace", b"grabar"), B("🔑 Sesión IG", b"sesion")],
            [B("📋 Perfiles a grabar", b"perfiles"), B("🩺 Diagnóstico", b"diag")],
            [B("❓ Ayuda", b"ayuda")],
        ]

    def estado_text(self):
        ig = ("@" + html.escape(str(self.ig.user))) if self.ig.ok else "❌ sin sesión"
        lines = [f"📊 <b>Estado</b>\n\n👤 Instagram: {ig}\n{self.following_line()}"]
        if self.active:
            lines.append(f"🔴 Grabando ahora ({len(self.active)}):")
            for r in self.active.values():
                lines.append(f"  • @{html.escape(r.user)} – {fmt_dur(time.time() - r.t0)}")
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
                lines.append(f"• @{html.escape(r.user)} – {fmt_dur(time.time() - r.t0)}")
                rows.append([B(f"⏹ Detener @{r.user}", f"stop:{bid}".encode())])
            return "\n".join(lines), rows + [[B("🔄 Actualizar", b"vivo")], back]
        if key == "grabar":
            self.pending = "grabar"
            return (
                "🔗 <b>Grabar un live por enlace</b>\n\n"
                "Envíame ahora el enlace del live de Instagram, o solo el @usuario si está en vivo en este momento.\n\n"
                "Ejemplos:\n<code>https://www.instagram.com/usuario/live/</code>\n<code>@usuario</code>\n\n"
                "También puedes pegar un enlace en cualquier momento, sin abrir este menú."
            ), [back]
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
        if pend == "grabar" or (pend is None and LINK_RE.search(text)):
            msg = await event.reply("⏳ Buscando el live…")
            await msg.edit(await self.record_target(text), buttons=back)
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
            msg = await reply("⏳ Buscando el live…")
            await msg.edit(await self.record_target(" ".join(args)), buttons=back)
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
            await rec.run()
        except Exception as e:
            rec.fail_reason = f"error interno: {str(e)[:200]}"
            log.exception("Error grabando @%s: %s", rec.user, e)
        finally:
            self.active.pop(rec.id, None)
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
            if bid not in self.notified:
                self.notified.add(bid)
                await self.notify(
                    f"🔴 @{b['username']} está en vivo (detectado por: {b.get('via') or '?'}). "
                    "Grabando en máxima calidad…"
                )
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
        self.chat = await self.resolve_chat()

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
