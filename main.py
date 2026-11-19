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
from telethon import TelegramClient, events
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


async def pick_best_streams(url):
    """Elige el video de mayor resolución/bitrate y el mejor audio del manifiesto."""
    rc, out, _ = await run_cmd(
        "ffprobe", "-v", "error", "-show_streams", "-of", "json", url, timeout=90
    )
    v = a = None
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
    return v, a


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
            "ignore": [],          # usuarios que NO se graban
            "only": [],            # si no está vacío: solo se graban estos
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
        self._endpoint = None
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
    def live_broadcasts(self):
        cl = self.cl
        res = None
        errs = []
        attempts = [self._endpoint] if self._endpoint else ["tray_get", "tray_post"]
        for name in attempts:
            try:
                if name == "tray_get":
                    res = cl.private_request("feed/reels_tray/")
                else:
                    res = cl.private_request(
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
                if isinstance(res, dict) and ("broadcasts" in res or "tray" in res):
                    self._endpoint = name
                    break
                res = None
            except Exception as e:
                msg = str(e).lower()
                if any(k in msg for k in ("login_required", "checkpoint", "challenge_required")):
                    raise
                errs.append(f"{name}: {e}")
                res = None
        if res is None:
            raise RuntimeError("No pude leer el tray de IG: " + " | ".join(errs)[:300])

        raw = list(res.get("broadcasts") or [])
        for item in res.get("tray") or []:
            if isinstance(item, dict) and item.get("broadcast"):
                raw.append(item["broadcast"])

        out = {}
        for b in raw:
            owner = b.get("broadcast_owner") or {}
            status = b.get("broadcast_status")
            if status not in (None, "active", "interrupted"):
                continue
            url = b.get("dash_playback_url") or b.get("dash_abr_playback_url")
            if not (b.get("id") and owner.get("username") and url):
                continue
            out[str(b["id"])] = {
                "id": str(b["id"]),
                "username": owner["username"],
                "url": url,
                "abr": b.get("dash_abr_playback_url"),
                "title": b.get("broadcast_message") or "",
            }
        return list(out.values())


# ============================================================================
# GRABACIÓN DE UN LIVE  (ffmpeg, calidad máxima, sin recomprimir)
# ============================================================================
class Recording:
    def __init__(self, app, b):
        self.app = app
        self.b = b
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
        v, a = await pick_best_streams(url)
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

    # ---------- Telegram ----------
    async def notify(self, text):
        try:
            await self.client.send_message(CFG.admin_id, text)
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
                        force_document=False, part_size_kb=512,
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
        if u in d["ignore"]:
            return False
        return (not d["only"]) or (u in d["only"])

    # ---------- comandos ----------
    HELP = (
        "🎥 *Grabador de lives de Instagram*\n\n"
        "/login usuario clave [codigo2FA] – iniciar sesión\n"
        "/sessionid VALOR – iniciar sesión con la cookie (más confiable)\n"
        "/estado – qué se está grabando\n"
        "/ignorar usuario – no grabar a esa cuenta\n"
        "/permitir usuario – volver a grabarla\n"
        "/solo usuario1 usuario2 – grabar SOLO a esas cuentas\n"
        "/todos – grabar a todas las que sigues\n"
        "/lista – ver filtros activos"
    )

    async def on_command(self, event):
        text = (event.raw_text or "").strip()
        if not text.startswith("/"):
            return
        cmd, *args = text.split()
        cmd = cmd.split("@")[0].lower()
        reply = event.reply

        if cmd in ("/start", "/ayuda", "/help"):
            await reply(self.HELP, parse_mode="md")

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
            await msg.edit(txt)

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
            await msg.edit(txt)

        elif cmd == "/estado":
            lines = [f"👤 Instagram: {'@' + str(self.ig.user) if self.ig.ok else '❌ sin sesión'}"]
            if self.active:
                lines.append(f"🔴 Grabando ahora ({len(self.active)}):")
                for r in self.active.values():
                    lines.append(f"  • @{r.user} – {fmt_dur(time.time() - r.t0)}")
            else:
                lines.append("⚪ Nadie en vivo ahora (o no sigues a nadie en vivo).")
            left = max(0, CFG.max_runtime - (time.time() - self.t0))
            lines.append(f"⏳ Turno actual termina en {fmt_dur(left)} (se relanza solo)")
            await reply("\n".join(lines))

        elif cmd == "/ignorar" and args:
            u = args[0].lstrip("@").lower()
            if u not in self.state.data["ignore"]:
                self.state.data["ignore"].append(u)
            await asyncio.to_thread(self.state.save)
            await reply(f"🚫 No grabaré a @{u}")

        elif cmd == "/permitir" and args:
            u = args[0].lstrip("@").lower()
            if u in self.state.data["ignore"]:
                self.state.data["ignore"].remove(u)
            await asyncio.to_thread(self.state.save)
            await reply(f"✅ @{u} vuelve a grabarse")

        elif cmd == "/solo" and args:
            self.state.data["only"] = [a.lstrip("@").lower() for a in args]
            await asyncio.to_thread(self.state.save)
            await reply("🎯 Solo grabaré: " + ", ".join("@" + a for a in self.state.data["only"]))

        elif cmd == "/todos":
            self.state.data["only"] = []
            await asyncio.to_thread(self.state.save)
            await reply("🌐 Grabaré a todas las cuentas que sigues.")

        elif cmd == "/lista":
            d = self.state.data
            await reply(
                f"🚫 Ignorados: {', '.join(d['ignore']) or '—'}\n"
                f"🎯 Solo: {', '.join(d['only']) or '— (todos)'}"
            )
        else:
            await reply("Comando no reconocido. Usa /ayuda")

    async def _try_delete(self, event):
        try:
            await event.delete()   # borra tu mensaje con la clave
        except Exception:
            pass

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
            log.exception("Error grabando @%s: %s", rec.user, e)
        finally:
            self.active.pop(rec.id, None)
            if time.time() - rec.t0 < 90:
                self.cooldown[rec.id] = time.time() + 90
            if rec.sent:
                await self.notify(f"✅ Live de @{rec.user} guardado en Telegram ({rec.sent} parte/s).")

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
            rec = Recording(self, b)
            self.active[bid] = rec
            rec.task = asyncio.create_task(self._run_rec(rec))
            if bid not in self.notified:
                self.notified.add(bid)
                await self.notify(f"🔴 @{b['username']} está en vivo. Grabando en máxima calidad…")
        for bid, rec in list(self.active.items()):
            if bid not in current:
                rec.missing += 1
                if rec.missing >= 3:
                    rec.request_stop()

    async def poll_loop(self):
        errors = 0
        last_save = time.time()
        while not self.stop_event.is_set() and time.time() - self.t0 < CFG.max_runtime:
            wait = CFG.poll + random.uniform(0, 10)
            if not self.ig.ok:
                await self.sleep(20)
                continue
            try:
                lives = await asyncio.to_thread(self.ig.live_broadcasts)
                errors = 0
                await self.handle_lives(lives)
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
            self.on_command, events.NewMessage(incoming=True, from_users=CFG.admin_id)
        )
        loop = asyncio.get_running_loop()
        for sig in (signal.SIGTERM, signal.SIGINT):
            try:
                loop.add_signal_handler(sig, self.stop_event.set)
            except NotImplementedError:
                pass

        if not self.ig.ok:
            await self.notify(
                "👋 Bot activo, pero falta iniciar sesión en Instagram.\n"
                "Envíame /sessionid VALOR o /login usuario clave (mira /ayuda)."
            )
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
