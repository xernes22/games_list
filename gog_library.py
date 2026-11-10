#!/usr/bin/env python3
"""Bibliothèque de jeux : génère une page HTML autonome (GOG, Epic Games, Steam, Ubisoft, Prime Gaming).

Usage :
    python3 gog_library.py                    ouvre l'interface dans le navigateur
    python3 gog_library.py --auto             génère la page sans interface
    python3 gog_library.py --auto --previous ANCIENNE.html --taille legere
    python3 gog_library.py --auto --par-plateforme                       page unique + une page par plateforme
    python3 gog_library.py --auto --par-plateforme --sans-page-unique    seulement une page par plateforme
    python3 gog_library.py --nettoyer         supprime les fichiers de l'ancienne version
    python3 gog_library.py --install-shortcut ajoute un lanceur au menu des applications
    python3 gog_library.py --diagnostic       teste le réseau et les certificats SSL
    python3 gog_library.py --out CHEMIN.html  choisit le fichier de sortie

Aucune base de données : l'historique (pour repérer les nouveaux jeux), les jaquettes réduites
(WebP/JPEG en base64) et les listes manuelles sont conservés dans la page HTML générée, qui sert
d'« ancien fichier » à la génération suivante. Seuls les jetons de connexion sont enregistrés
(~/.config/gog-bibliotheque). Pillow (ou ImageMagick) sert à réduire les images.
"""
import argparse
import base64
import difflib
import hashlib
import html
import io
import json
import os
import re
import secrets
import shutil
import struct
import subprocess
import sys
import threading
import time
import unicodedata
import uuid
import zlib
import urllib.error
import urllib.request
try:
    import ssl
except ImportError:  # Python compilé sans OpenSSL (ex. python3Minimal) : module _ssl absent
    ssl = None
import webbrowser
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, urlencode, urlparse

# --- Numérotation : « vN.NN » (v0.26, v0.27, …). Le nombre augmente de 1 à chaque version livrée,
# qu'il s'agisse d'une nouveauté ou d'une correction. v0.25 est la version de référence
# (c'est l'ancienne « 2.5.0 »). Historique :
#   anciennes versions (ancien format MAJEUR.MINEUR.CORRECTIF) :
#     0.1  gog_to_html.py : page hors ligne des jaquettes GOG        0.2  cache + badge « Nouveau »
#     1.0  application avec interface locale (GOG)                   1.1  dossier Téléchargements, liens
#     1.2  Epic Games                                                1.3  fusion des doublons, choix du site
#     1.4  vérification des connexions au démarrage                  1.5  Steam, listes Ubisoft / Prime
#     1.6  NixOS : certificats SSL, diagnostic, secours curl
#     2.0  plus de base locale (historique dans la page), SteamGridDB, images réduites en base64
#     2.1  panneaux connexions / listes, correctif réutilisation     2.2  conversion WebP multi-outils
#     2.3  interface en deux colonnes responsive                     2.4  pages par plateforme
#   nouveau format :
#     v0.25  (ex-2.5.0) deux cases : fichier unique / par plateforme, version affichée   <- RÉFÉRENCE
#     v0.26  nouveau format de numérotation, documentation de l'en-tête, import inutilisé retiré
#     v0.27  Ubisoft Connect et Prime Gaming par connexion (méthode de Lutris), liste manuelle en secours
#     v0.28  itch.io (clé API), images en paysage gardées entières sur fond flou
#     v0.29  Ubisoft : confirmation de session comme Lutris, erreurs détaillées, renouvellement anticipé
#     v0.30  Ubisoft : instructions précisées (la page 404 après la connexion est normale)
#     v0.31  Ubisoft : script de console tolérant (stockage refusé par le navigateur), erreurs signalées
#     v0.32  Ubisoft : la session est lue sur la page change_domain (comme Lutris), bouton dédié
#     v0.33  Ubisoft : méthode alternative sans stockage du navigateur (réponse de connexion, onglet Réseau)
#     v0.34  Ubisoft : textes simplifiés ; jeux sans page de boutique : redirection vers Steam après 5 s
VERSION = "0.34"
FORMAT = 3  # version du format des données intégrées dans les pages (indépendante du numéro de version)


def version_label():
    return f"v{VERSION}"


CONFIG = Path(os.environ.get("XDG_CONFIG_HOME", Path.home() / ".config")) / "gog-bibliotheque"
BADGE_DAYS = 30
MANUAL = {}   # listes manuelles (Ubisoft, Prime) : en mémoire, conservées dans la page HTML
CTX = {"epic": {}, "epic_seen": set(), "lookup": {}, "noshrink": False}  # caches de la génération
PRESETS = {"legere": (160, 55), "standard": (200, 62), "haute": (300, 70)}  # (largeur px, qualité)
SGDB_API = "https://www.steamgriddb.com/api/v2"


def preset_of(width):
    return next((n for n, (w, _) in PRESETS.items() if w == width), "standard")


def downloads_dir():
    """Dossier de téléchargements de l'utilisateur (celui des navigateurs)."""
    home = Path.home()
    cfg = Path(os.environ.get("XDG_CONFIG_HOME", home / ".config")) / "user-dirs.dirs"
    try:
        for line in cfg.read_text(encoding="utf-8").splitlines():
            if line.startswith("XDG_DOWNLOAD_DIR="):
                val = line.split("=", 1)[1].strip().strip('"')
                p = Path(val.replace("$HOME", str(home)))
                if p.is_dir() and p != home:
                    return p
    except OSError:
        pass
    for name in ("Downloads", "Téléchargements"):
        if (home / name).is_dir():
            return home / name
    return home


OUTPUT = downloads_dir() / "ma_bibliotheque_jeux.html"


class NotLoggedIn(Exception):
    pass


# ------------------------------------------------------------------ utilitaires
def _make_ssl_context():
    """Contexte SSL qui retrouve les certificats même sur NixOS / environnements Nix,
    où Python ne connaît parfois pas l'emplacement du bundle de certificats."""
    if ssl is None:
        return None, ""
    ctx = ssl.create_default_context()
    candidates = [os.environ.get("SSL_CERT_FILE"), os.environ.get("NIX_SSL_CERT_FILE"),
                  "/etc/ssl/certs/ca-certificates.crt", "/etc/ssl/certs/ca-bundle.crt",
                  "/etc/pki/tls/certs/ca-bundle.crt", "/etc/ssl/cert.pem",
                  "/run/current-system/sw/etc/ssl/certs/ca-bundle.crt"]
    try:
        import certifi
        candidates.append(certifi.where())
    except ImportError:
        pass
    for c in candidates:
        if c and os.path.isfile(c):
            try:
                ctx.load_verify_locations(cafile=c)
                return ctx, c
            except (ssl.SSLError, OSError):
                continue
    return ctx, ""


SSL_CONTEXT, CA_BUNDLE = _make_ssl_context()


def net_error(e, site):
    """Message lisible pour une erreur réseau (hors réponse d'erreur HTTP)."""
    reason = getattr(e, "reason", e)
    if ((ssl is not None and isinstance(reason, ssl.SSLCertVerificationError))
            or "CERTIFICATE_VERIFY_FAILED" in str(reason)):
        return (f"certificats SSL non reconnus pour joindre {site} ({reason}). Sur NixOS ou Nix : "
                "ajoute le paquet « cacert » et lance avec "
                "SSL_CERT_FILE=/etc/ssl/certs/ca-bundle.crt")
    return f"impossible de joindre {site} : {reason}"


def redact(text):
    """Masque les clés, jetons et codes qui pourraient apparaître dans un message d'erreur."""
    text = re.sub(r"(?i)\b(Ubi_v1|rm_v1)\s+t=[^\s)&\"']+", r"\1 t=***", str(text))
    return re.sub(r"(?i)\b(key|api_key|token|access_token|ticket|code)=[^&\s)\"']+", r"\1=***", text)


def describe(e, site):
    if isinstance(e, urllib.error.HTTPError):
        return f"{site} a répondu avec l'erreur HTTP {e.code}"
    if isinstance(e, urllib.error.URLError):
        return redact(net_error(e, site))
    return redact(e)


def http_detail(e):
    try:
        d = json.loads(e.read())
        return str(d.get("errorMessage") or d.get("error_description") or d.get("errorCode") or "")
    except Exception:
        return ""


CURL = None if ssl is not None else shutil.which("curl")
NO_TLS_HELP = (
    "Ton Python n'a pas de support SSL (module _ssl absent) : il ne peut pas ouvrir de pages "
    "HTTPS. Cela arrive avec « python3Minimal » ou un Python compilé sans OpenSSL.\n"
    "  - Utilise le paquet Python complet. Sous Nix :\n"
    "      nix-shell -p python3 cacert xdg-utils --run 'python3 gog_library.py'\n"
    "    Test : python3 -c \"import ssl; print(ssl.OPENSSL_VERSION)\"\n"
    "  - Ou installe « curl » : l'application l'utilise automatiquement en secours.")


def _curl_quote(v):
    return ('"' + v.replace("\\", "\\\\").replace('"', '\\"')
            .replace("\n", "\\n").replace("\r", "\\r") + '"')


def _curl_request(url, headers, data, timeout, method=None):
    """Requête HTTPS via curl (secours si Python n'a pas SSL). Même comportement que urllib :
    lève HTTPError pour un statut >= 400 et URLError pour une panne réseau.
    La configuration passe par l'entrée standard : jetons et clés restent hors de `ps`."""
    cfg = [f"url = {_curl_quote(url)}", "silent", "show-error", "location",
           f"max-time = {int(timeout)}", 'write-out = "\\n__HTTP__%{http_code}"']
    cfg += [f"header = {_curl_quote(f'{k}: {v}')}" for k, v in headers.items()]
    if data is not None:
        cfg.append(f"data = {_curl_quote(data)}")
    if method in ("PUT", "DELETE", "PATCH"):
        cfg.append(f"request = {_curl_quote(method)}")
    try:
        r = subprocess.run([CURL, "--config", "-"], input="\n".join(cfg).encode(),
                           capture_output=True, timeout=timeout + 10)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise urllib.error.URLError(f"curl : {e}") from e
    out = r.stdout
    cut = out.rfind(b"\n__HTTP__")
    if r.returncode != 0 or cut < 0:
        msg = r.stderr.decode("utf-8", "replace").strip() or f"curl a échoué (code {r.returncode})"
        raise urllib.error.URLError(msg)
    code, body = int(out[cut + 9:] or 0), out[:cut]
    if code >= 400:
        raise urllib.error.HTTPError(url, code, f"HTTP {code}", {}, io.BytesIO(body))
    return body


def http_get(url, headers=None, timeout=25):
    h = {"User-Agent": "Mozilla/5.0"}
    h.update(headers or {})
    if ssl is None:
        if not CURL:
            raise urllib.error.URLError(NO_TLS_HELP)
        return _curl_request(url, h, None, timeout)
    with urllib.request.urlopen(urllib.request.Request(url, headers=h), timeout=timeout,
                                context=SSL_CONTEXT) as r:
        return r.read()


def http_post(url, data, headers=None, timeout=25):
    h = {"User-Agent": "Mozilla/5.0", "Content-Type": "application/x-www-form-urlencoded"}
    h.update(headers or {})
    if ssl is None:
        if not CURL:
            raise urllib.error.URLError(NO_TLS_HELP)
        return _curl_request(url, h, urlencode(data), timeout)
    req = urllib.request.Request(url, data=urlencode(data).encode(), headers=h, method="POST")
    with urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT) as r:
        return r.read()


def http_json(method, url, obj=None, headers=None, timeout=25):
    """Requête JSON (GET, POST ou PUT) ; retourne la réponse décodée ({} si elle est vide).
    Lève HTTPError (statut >= 400) ou URLError (panne réseau)."""
    h = {"User-Agent": "Mozilla/5.0", "Accept": "application/json"}
    h.update(headers or {})
    body = None if obj is None else json.dumps(obj)
    if body is not None:
        h.setdefault("Content-Type", "application/json")
    if ssl is None:
        if not CURL:
            raise urllib.error.URLError(NO_TLS_HELP)
        raw = _curl_request(url, h, body, timeout, method=method)
    else:
        data = body.encode() if body is not None else (b"" if method in ("POST", "PUT") else None)
        req = urllib.request.Request(url, data=data, headers=h, method=method)
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT) as r:
            raw = r.read()
    return json.loads(raw) if raw.strip() else {}


def write_private(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj), encoding="utf-8")
    os.chmod(path, 0o600)


def mime_of(data):
    if data[:4] == b"\x89PNG":
        return "image/png"
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "image/webp"
    if data[:3] == b"GIF":
        return "image/gif"
    return "image/jpeg"


def _pillow_encode(data, width, quality):
    from PIL import Image, ImageFilter, ImageOps
    im = Image.open(io.BytesIO(data))
    im.load()
    if "A" in im.getbands():  # transparence : fond sombre
        rgba = im.convert("RGBA")
        im = Image.new("RGB", rgba.size, (24, 24, 32))
        im.paste(rgba, mask=rgba.getchannel("A"))
    else:
        im = im.convert("RGB")
    if im.width >= im.height:  # paysage ou carré : l'image entière sur un fond flou, sans recadrage
        tw, th = width, int(width * 1.5)
        back = ImageOps.fit(im, (tw, th), method=Image.BILINEAR).filter(ImageFilter.GaussianBlur(10))
        im_fg = ImageOps.contain(im, (tw, th), method=Image.LANCZOS)
        back = Image.blend(back, Image.new("RGB", (tw, th), (24, 24, 32)), 0.45)
        back.paste(im_fg, ((tw - im_fg.width) // 2, (th - im_fg.height) // 2))
        im = back
    else:
        tw = max(16, min(width, im.width, int(im.height / 1.5)))
        im = ImageOps.fit(im, (tw, int(tw * 1.5)), method=Image.LANCZOS, centering=(0.5, 0.35))
    buf = io.BytesIO()
    try:
        im.save(buf, "WEBP", quality=quality, method=6)
        return buf.getvalue(), "image/webp"
    except Exception:
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=quality, optimize=True, progressive=True)
        return buf.getvalue(), "image/jpeg"


def _magick_encode(data, width, quality):
    """Secours sans Pillow : ImageMagick (magick / convert) ou GraphicsMagick (gm)."""
    h = int(width * 1.5)
    for cmd in (["magick"], ["convert"], ["gm", "convert"]):
        exe = shutil.which(cmd[0])
        if not exe:
            continue
        for fmt, mime in (("webp", "image/webp"), ("jpeg", "image/jpeg")):
            try:
                r = subprocess.run([exe, *cmd[1:], "-", "-resize", f"{width}x{h}^", "-gravity",
                                    "center", "-extent", f"{width}x{h}", "-quality", str(quality),
                                    f"{fmt}:-"], input=data, capture_output=True, timeout=30)
                if r.returncode == 0 and r.stdout:
                    return r.stdout, mime
            except (OSError, subprocess.TimeoutExpired):
                pass
    return None


def _ffmpeg_encode(data, width, quality):
    """Secours sans Pillow ni ImageMagick : ffmpeg (encodeur libwebp)."""
    exe = shutil.which("ffmpeg")
    if not exe:
        return None
    h = int(width * 1.5)
    try:
        r = subprocess.run([exe, "-loglevel", "error", "-i", "pipe:0", "-vf",
                            f"scale={width}:{h}:force_original_aspect_ratio=increase,crop={width}:{h}",
                            "-frames:v", "1", "-c:v", "libwebp", "-quality", str(quality),
                            "-f", "webp", "pipe:1"], input=data, capture_output=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return (r.stdout, "image/webp") if r.returncode == 0 and r.stdout else None


ENCODERS = [("Pillow", _pillow_encode), ("ImageMagick", _magick_encode), ("ffmpeg", _ffmpeg_encode)]
_PROBE = None
MAX_RAW = 80_000  # sans outil de conversion, les images plus lourdes ne sont pas intégrées


def _probe_png():
    """Minuscule PNG généré à la volée, pour tester les outils de conversion."""
    def chunk(kind, body):
        return (struct.pack(">I", len(body)) + kind + body
                + struct.pack(">I", zlib.crc32(kind + body) & 0xFFFFFFFF))
    w, h = 8, 12
    raw = b"".join(b"\x00" + b"\x30\x60\x90" * w for _ in range(h))
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw)) + chunk(b"IEND", b""))


def probe_image_tool():
    """Premier outil de conversion qui fonctionne vraiment : (nom, type MIME, fonction).
    Le WebP est préféré ; ("", "", None) si aucun outil n'est disponible."""
    global _PROBE
    if _PROBE is None:
        png, best = _probe_png(), None
        for name, fn in ENCODERS:
            try:
                res = fn(png, 200, 60)
            except Exception:
                continue
            if res and res[0]:
                if res[1] == "image/webp":
                    best = (name, res[1], fn)
                    break
                best = best or (name, res[1], fn)
        _PROBE = best or ("", "", None)
    return _PROBE


def image_tool_info():
    name, mime, _ = probe_image_tool()
    return {"tool": name, "format": {"image/webp": "WebP", "image/jpeg": "JPEG"}.get(mime, "")}


def looks_like_image(data):
    return (data[:2] == b"\xff\xd8" or data[:4] == b"\x89PNG" or data[:3] == b"GIF"
            or (data[:4] == b"RIFF" and data[8:12] == b"WEBP"))


def needs_convert(uri):
    """Image déjà intégrée dans un format ou un poids que nos outils ne produiraient pas
    (par exemple un PNG d'origine gardé tel quel faute d'outil de conversion)."""
    m = re.match(r"data:([^;,]+)", uri)
    return not m or m.group(1) not in ("image/webp", "image/jpeg") or len(uri) > 120_000


def process_image(data, width, quality):
    """Réduit l'image (format 2:3) et la renvoie en data URI base64 (WebP, sinon JPEG).
    Retourne "" si l'image est illisible ou, sans aucun outil de conversion, trop lourde."""
    fn = probe_image_tool()[2]
    if fn is None:
        CTX["noshrink"] = True
        if not data or len(data) > MAX_RAW or not looks_like_image(data):
            return ""
        out, mime = data, mime_of(data)
    else:
        try:
            res = fn(data, width, quality)
        except Exception:
            return ""
        if not res:
            return ""
        out, mime = res
    return f"data:{mime};base64,{base64.b64encode(out).decode()}"


# ------------------------------------------------------------------ boutiques
class Store:
    id = name = tag = token_file = auth_url = placeholder = help = ""
    kind = "oauth"          # oauth : connexion via le site | key : clé API | manual : liste saisie
    steps = []
    fields = []
    service = False         # True : service annexe (images), pas une boutique
    has_list = False        # True : la plateforme accepte aussi une liste manuelle
    snippet = ""            # script à coller dans la console du navigateur (connexion par copie)
    last_error = ""         # détail de la dernière erreur de connexion (affiché à l'utilisateur)
    extra_links = []        # boutons supplémentaires dans le panneau de connexion [{"label", "url"}]
    alt_title, alt_steps = "", []  # méthode alternative de connexion (étapes repliables)

    def count(self):
        return 0

    def connected(self):
        return self.logged_in()

    def __init__(self):
        self._lock = threading.RLock()  # évite deux rafraîchissements simultanés

    def access_token(self):
        with self._lock:
            if not self.tokens_path.exists():
                raise NotLoggedIn()
            t = json.loads(self.tokens_path.read_text("utf-8"))
            if time.time() > t["expires_at"] - 60:
                try:
                    self._refresh(t["refresh_token"])
                except urllib.error.HTTPError as e:  # refusé par la boutique : session perdue
                    raise NotLoggedIn() from e
                # (une panne réseau se propage telle quelle : la session n'est pas perdue)
                t = json.loads(self.tokens_path.read_text("utf-8"))
            return t["access_token"]

    def check(self):
        """État de la connexion : none / ok / expired / offline."""
        if not self.connected():
            return {"state": "none"}
        try:
            return {"state": "ok", "user": self.verify()}
        except NotLoggedIn:
            self.logout()
            return {"state": "expired", "detail": self.last_error}
        except Exception as e:
            return {"state": "offline", "detail": describe(e, self.name)[:300]}

    @property
    def tokens_path(self):
        return CONFIG / self.token_file

    def logged_in(self):
        return self.tokens_path.exists()

    def logout(self):
        self.tokens_path.unlink(missing_ok=True)
        try:
            CONFIG.rmdir()  # supprime le dossier de configuration s'il est devenu vide
        except OSError:
            pass

    def info(self):
        return {"id": self.id, "name": self.name, "logged": self.connected(),
                "usable": self.logged_in(), "auth_url": self.auth_url, "steps": self.steps,
                "placeholder": self.placeholder, "kind": self.kind,
                "fields": self.fields, "help": self.help, "count": self.count(),
                "service": self.service, "has_list": self.has_list, "snippet": self.snippet,
                "extra_links": self.extra_links, "alt_title": self.alt_title,
                "alt_steps": self.alt_steps}


# ---- GOG (client public GOG Galaxy, comme Heroic / Minigalaxy)
GOG_CLIENT_ID = "46899977096215655"
GOG_CLIENT_SECRET = "9d85c43b1482497dbbce61f6e4aa173a433796eeae2ca8c5f6129f2dc4de46d9"
GOG_REDIRECT = "https://embed.gog.com/on_login_success?origin=client"
GOG_SUFFIXES = ["_product_card_v2_mobile_slider_293.jpg", ".jpg"]


class GOGStore(Store):
    id, name, tag, token_file = "gog", "GOG", "GOG", "tokens.json"
    auth_url = "https://auth.gog.com/auth?" + urlencode({
        "client_id": GOG_CLIENT_ID, "redirect_uri": GOG_REDIRECT,
        "response_type": "code", "layout": "galaxy"})
    placeholder = "https://embed.gog.com/on_login_success?origin=client&code=…"
    steps = ["Clique sur le bouton et connecte-toi sur gog.com.",
             "Une page vide ou d'erreur s'affiche ensuite : c'est normal. "
             "Copie son adresse (Ctrl+L puis Ctrl+C).",
             "Reviens ici et clique sur « Coller et valider » (ou Ctrl+V dans le champ)."]

    def _save(self, d):
        write_private(self.tokens_path, {
            "access_token": d["access_token"], "refresh_token": d["refresh_token"],
            "expires_at": time.time() + int(d.get("expires_in", 3600))})

    def _token_request(self, **params):
        params.update(client_id=GOG_CLIENT_ID, client_secret=GOG_CLIENT_SECRET)
        return json.loads(http_get("https://auth.gog.com/token?" + urlencode(params)))

    @staticmethod
    def extract_code(text):
        text = text.strip()
        if "code=" in text:
            q = parse_qs(urlparse(text).query)
            if q.get("code"):
                return q["code"][0]
        return text

    def login(self, text):
        code = self.extract_code(text)
        if not code:
            raise ValueError("Adresse ou code vide.")
        try:
            self._save(self._token_request(grant_type="authorization_code",
                                           code=code, redirect_uri=GOG_REDIRECT))
        except urllib.error.HTTPError as e:
            raise ValueError(f"Connexion refusée par GOG (HTTP {e.code}). Recommence la connexion : "
                             "le code expire vite, ne sert qu'une fois et doit être copié en entier.") from e
        except urllib.error.URLError as e:
            raise ValueError("Connexion impossible : " + net_error(e, "GOG")) from e

    def _refresh(self, refresh_token):
        self._save(self._token_request(grant_type="refresh_token", refresh_token=refresh_token))

    def verify(self):
        """Vérifie la session auprès de GOG ; retourne le nom d'utilisateur."""
        try:
            d = json.loads(http_get("https://embed.gog.com/userData.json",
                                    {"Authorization": f"Bearer {self.access_token()}"}))
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise NotLoggedIn() from e
            raise
        if d.get("isLoggedIn") is False:
            raise NotLoggedIn()
        return d.get("username", "")

    def fetch(self, progress):
        games, page, total = [], 1, 1
        while page <= total:
            url = f"https://embed.gog.com/account/getFilteredProducts?mediaType=1&page={page}"
            try:
                d = json.loads(http_get(url, {"Authorization": f"Bearer {self.access_token()}"}))
            except urllib.error.HTTPError as e:
                if e.code in (401, 403):
                    raise NotLoggedIn() from e
                raise
            total = d.get("totalPages", 1)
            for p in d["products"]:
                slug, img = p.get("slug", ""), p.get("image") or ""
                if img.startswith("//"):
                    img = "https:" + img
                games.append({
                    "title": p["title"], "skey": "gog:" + (slug or p["title"]), "cover_base": img,
                    "cover_urls": [img + s for s in GOG_SUFFIXES] if img else [],
                    "link": ("https://www.gog.com/game/" + quote(slug)) if slug else ""})
            progress("GOG : lecture de la bibliothèque", page, total)
            page += 1
        return games


# ---- Epic Games (client public du lanceur Epic, comme Legendary / Heroic)
EPIC_CLIENT_ID = "34a02cf8f4414e29b15921876da36f9a"
EPIC_CLIENT_SECRET = "daafbccc737745039dffe53d94fc76cf"
EPIC_UA = "UELauncher/11.0.1-14907503+++Portal+Release-Live Windows/10.0.19041.1.256.64bit"
EPIC_TOKEN_URL = "https://account-public-service-prod03.ol.epicgames.com/account/api/oauth/token"
EPIC_LIBRARY = "https://library-service.live.use1a.on.epicgames.com/library/api/public/items"
EPIC_VERIFY = "https://account-public-service-prod03.ol.epicgames.com/account/api/oauth/verify"
EPIC_ACCOUNT = "https://account-public-service-prod03.ol.epicgames.com/account/api/public/account/"
EPIC_CATALOG = ("https://catalog-public-service-prod06.ol.epicgames.com"
                "/catalog/api/shared/namespace/{ns}/bulk/items")
EPIC_IMG_PREF = ["DieselGameBoxTall", "OfferImageTall", "DieselStoreFrontTall",
                 "Thumbnail", "DieselGameBox", "OfferImageWide", "DieselStoreFrontWide"]
EPIC_EXCLUDED = {"addons", "digitalextras", "editors", "plugins"}


class EpicStore(Store):
    id, name, tag, token_file = "epic", "Epic Games", "EPIC", "epic_tokens.json"
    auth_url = ("https://www.epicgames.com/id/login?redirectUrl=" + quote(
        "https://www.epicgames.com/id/api/redirect?clientId=" + EPIC_CLIENT_ID
        + "&responseType=code", safe=""))
    placeholder = '{"authorizationCode":"…"}'
    steps = ["Clique sur le bouton et connecte-toi sur epicgames.com.",
             "Sur la page de texte qui s'affiche, fais Ctrl+A puis Ctrl+C "
             "(le code est extrait tout seul, inutile de le chercher).",
             "Reviens ici et clique sur « Coller et valider » (ou Ctrl+V dans le champ). "
             "Le code expire vite et ne sert qu'une fois : ne le partage pas."]

    @staticmethod
    def extract_code(text):
        text = text.strip()
        try:
            d = json.loads(text)
            if isinstance(d, dict) and d.get("authorizationCode"):
                return str(d["authorizationCode"])
        except ValueError:
            pass
        m = re.search(r"[0-9a-f]{32}", text)
        return m.group(0) if m else text.strip('"\' ')

    def _token_post(self, **data):
        basic = base64.b64encode(f"{EPIC_CLIENT_ID}:{EPIC_CLIENT_SECRET}".encode()).decode()
        data["token_type"] = "eg1"
        return json.loads(http_post(EPIC_TOKEN_URL, data, {
            "Authorization": "basic " + basic, "User-Agent": EPIC_UA}))

    def _save(self, d):
        write_private(self.tokens_path, {
            "access_token": d["access_token"], "refresh_token": d["refresh_token"],
            "expires_at": time.time() + int(d.get("expires_in", 3600)),
            "account_id": d.get("account_id", "")})

    def login(self, text):
        code = self.extract_code(text)
        if not code:
            raise ValueError("Texte vide.")
        try:
            self._save(self._token_post(grant_type="authorization_code", code=code))
        except urllib.error.HTTPError as e:
            detail = http_detail(e)
            raise ValueError(f"Connexion refusée par Epic (HTTP {e.code}"
                             + (f" : {detail}" if detail else "") + "). Recommence la connexion : "
                             "le code expire vite et ne sert qu'une fois.") from e
        except urllib.error.URLError as e:
            raise ValueError("Connexion impossible : " + net_error(e, "Epic")) from e

    def _refresh(self, refresh_token):
        self._save(self._token_post(grant_type="refresh_token", refresh_token=refresh_token))

    def verify(self):
        """Vérifie la session auprès d'Epic ; retourne le nom affiché (si disponible)."""
        hdr = {"Authorization": "bearer " + self.access_token(), "User-Agent": EPIC_UA}
        try:
            d = json.loads(http_get(EPIC_VERIFY, hdr))
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise NotLoggedIn() from e
            raise
        try:
            acc = json.loads(http_get(EPIC_ACCOUNT + quote(d["account_id"]), hdr))
            return acc.get("displayName", "")
        except Exception:
            return ""

    @staticmethod
    def parse_catalog(info):
        top = {c.get("path", "").split("/")[0] for c in info.get("categories", [])}
        keep = ("games" in top and not info.get("mainGameItem")
                and not (top & EPIC_EXCLUDED))
        imgs = {k.get("type"): k.get("url") for k in info.get("keyImages", [])}
        image = next((imgs[t] for t in EPIC_IMG_PREF if imgs.get(t)), "")
        return {"title": info.get("title", ""), "keep": keep, "image": image}

    def fetch(self, progress):
        auth = {"Authorization": "bearer " + self.access_token(), "User-Agent": EPIC_UA}
        records, cursor = [], None
        while True:
            params = {"includeMetadata": "true"}
            if cursor:
                params["cursor"] = cursor
            try:
                d = json.loads(http_get(EPIC_LIBRARY + "?" + urlencode(params), auth))
            except urllib.error.HTTPError as e:
                if e.code in (401, 403):
                    raise NotLoggedIn() from e
                raise
            records += d.get("records", [])
            cursor = (d.get("responseMetadata") or {}).get("nextCursor")
            progress("Epic : lecture de la bibliothèque", len(records), 0)
            if not cursor:
                break

        uniq = {}
        for r in records:
            if r.get("namespace") != "ue" and r.get("catalogItemId"):
                uniq.setdefault(r["catalogItemId"], r)

        cache = CTX["epic"]
        CTX["epic_seen"] = set(uniq)
        todo = [r for cid, r in uniq.items() if cid not in cache]
        done = 0
        lock = threading.Lock()

        def lookup(r):
            nonlocal done
            cid = r["catalogItemId"]
            try:
                url = EPIC_CATALOG.format(ns=r["namespace"]) + "?" + urlencode({
                    "id": cid, "includeDLCDetails": "true", "includeMainGameDetails": "true",
                    "country": "US", "locale": "en"})
                info = json.loads(http_get(url, auth)).get(cid)
                res = self.parse_catalog(info) if info else None
            except Exception:
                res = None
            with lock:
                done += 1
                progress("Epic : informations des jeux", done, len(todo))
            return cid, res

        if todo:
            with ThreadPoolExecutor(max_workers=8) as ex:
                for cid, res in ex.map(lookup, todo):
                    if res:
                        cache[cid] = res

        games = []
        for cid in uniq:
            e = cache.get(cid)
            if not e or not e["keep"] or not e["title"]:
                continue
            img = e["image"]
            sep = "&" if "?" in img else "?"
            games.append({
                "title": e["title"], "skey": "epic:" + cid, "cover_base": img,
                "cover_urls": [img + sep + "h=400&resize=1&w=300", img] if img else [],
                "link": ("https://store.epicgames.com/en-US/browse?q=" + quote(e["title"])
                         + "&sortBy=relevancy&sortDir=DESC&count=40")})
        return games


# ---- Steam (API web officielle : clé API gratuite + profil dont les jeux sont publics)
STEAM_API = "https://api.steampowered.com"


def steam_lookup(title):
    """Identifiant Steam d'un jeu (titre identique exigé) : appid, 0 si absent de Steam,
    None si la recherche a échoué (rien n'est alors mémorisé)."""
    key = norm_title(title)
    try:
        d = json.loads(http_get("https://store.steampowered.com/api/storesearch/?" +
                                urlencode({"term": title, "l": "english", "cc": "US"})))
        return next((x["id"] for x in d.get("items", []) if norm_title(x.get("name", "")) == key), 0)
    except Exception:
        return None


def steam_cover_urls(appid):
    base = f"https://cdn.cloudflare.steamstatic.com/steam/apps/{appid}/"
    return base + "library_600x900.jpg", [base + "library_600x900.jpg", base + "header.jpg"]


class SteamStore(Store):
    id, name, tag, token_file = "steam", "Steam", "STEAM", "steam_tokens.json"
    kind = "key"
    auth_url = "https://steamcommunity.com/dev/apikey"
    fields = [{"name": "key", "label": "Clé API Steam", "secret": True},
              {"name": "profile", "label": "Adresse de ton profil Steam (ou SteamID64)",
               "secret": False}]
    steps = ["Génère une clé API gratuite avec le bouton ci-dessous (au champ « nom de domaine », "
             "tu peux écrire localhost).",
             "Dans Steam : Profil > Modifier le profil > Paramètres de confidentialité, mets "
             "« Détails des jeux » sur Public (au moins pour la génération).",
             "Colle ta clé et l'adresse de ton profil ci-dessous. La clé reste sur ton ordinateur."]

    def _call(self, path, **params):
        try:
            return json.loads(http_get(f"{STEAM_API}{path}?" + urlencode(params)))
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise NotLoggedIn() from e
            raise

    def _cfg(self):
        if not self.tokens_path.exists():
            raise NotLoggedIn()
        return json.loads(self.tokens_path.read_text("utf-8"))

    def login_fields(self, v):
        key = (v.get("key") or "").strip()
        profile = (v.get("profile") or "").strip()
        if not re.fullmatch(r"[0-9A-Fa-f]{32}", key):
            raise ValueError("La clé API doit faire 32 caractères (chiffres et lettres A à F).")
        m = re.search(r"\b(7656119\d{10})\b", profile)
        steamid = m.group(1) if m else ""
        if not steamid:
            vanity = (re.sub(r".*/id/", "", profile.rstrip("/")) if "/id/" in profile
                      else profile.strip("/ "))
            if not re.fullmatch(r"[\w.-]{2,64}", vanity):
                raise ValueError("Adresse de profil non reconnue.")
            try:
                r = self._call("/ISteamUser/ResolveVanityURL/v1/", key=key, vanityurl=vanity)
            except NotLoggedIn:
                raise ValueError("Clé API refusée par Steam.")
            except Exception as e:
                raise ValueError("Connexion impossible : " + describe(e, "Steam")) from e
            resp = r.get("response", {})
            if resp.get("success") != 1:
                raise ValueError("Profil introuvable : vérifie l'adresse de ton profil.")
            steamid = resp["steamid"]
        write_private(self.tokens_path, {"api_key": key, "steamid": steamid})
        try:
            self.verify()
        except NotLoggedIn:
            self.logout()
            raise ValueError("Clé API refusée par Steam.")
        except Exception as e:
            self.logout()
            raise ValueError("Vérification impossible : " + describe(e, "Steam")) from e

    def verify(self):
        c = self._cfg()
        d = self._call("/ISteamUser/GetPlayerSummaries/v2/", key=c["api_key"], steamids=c["steamid"])
        players = d.get("response", {}).get("players", [])
        return players[0].get("personaname", "") if players else ""

    def fetch(self, progress):
        c = self._cfg()
        d = self._call("/IPlayerService/GetOwnedGames/v1/", key=c["api_key"], steamid=c["steamid"],
                       include_appinfo=1, include_played_free_games=1, format="json")
        owned = d.get("response", {}).get("games") or []
        progress("Steam : lecture de la bibliothèque", 1, 1)
        if not owned:
            raise ValueError("aucun jeu renvoyé : mets « Détails des jeux » sur Public "
                             "dans les paramètres de confidentialité de ton profil Steam")
        games, seen = [], set()
        for o in owned:
            appid, name = o.get("appid"), (o.get("name") or "").strip()
            if not appid or not name or appid in seen:
                continue
            seen.add(appid)
            base, urls = steam_cover_urls(appid)
            games.append({"title": name, "skey": f"steam:{appid}", "cover_base": base,
                          "cover_urls": urls,
                          "link": f"https://store.steampowered.com/app/{appid}"})
        return games


# ---- itch.io : clé API personnelle (la même méthode que Lutris)
ITCH_API = "https://api.itch.io"


class ItchStore(Store):
    id, name, tag, token_file = "itchio", "itch.io", "ITCH", "itchio_tokens.json"
    kind = "key"
    auth_url = "https://itch.io/user/settings/api-keys"
    fields = [{"name": "key", "label": "Clé API itch.io", "secret": True}]
    steps = ["Ouvre la page des clés API avec le bouton ci-dessous (connecte-toi à itch.io si besoin).",
             "Clique sur « Generate new API key » : donne-lui son propre nom, par exemple « bibliothèque ».",
             "Copie la clé et colle-la ci-dessous. Elle reste sur ton ordinateur et tu peux la révoquer "
             "à tout moment depuis cette même page."]

    def _call(self, path, **params):
        try:
            return http_json("GET", ITCH_API + path + ("?" + urlencode(params) if params else ""), None,
                             {"Authorization": "Bearer " + self._key()})
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise NotLoggedIn() from e
            raise

    def _key(self):
        if not self.tokens_path.exists():
            raise NotLoggedIn()
        return json.loads(self.tokens_path.read_text("utf-8"))["api_key"]

    def login_fields(self, v):
        key = (v.get("key") or "").strip()
        if not re.fullmatch(r"[A-Za-z0-9_-]{20,100}", key):
            raise ValueError("Clé API non reconnue (20 à 100 caractères, lettres et chiffres).")
        write_private(self.tokens_path, {"api_key": key})
        try:
            self.verify()
        except NotLoggedIn:
            self.logout()
            raise ValueError("Clé API refusée par itch.io : vérifie qu'elle est complète et non révoquée.")
        except Exception as e:
            self.logout()
            raise ValueError("Vérification impossible : " + describe(e, "itch.io")) from e

    def verify(self):
        user = (self._call("/profile") or {}).get("user")
        if not user:
            raise NotLoggedIn()
        return user.get("display_name") or user.get("username") or ""

    def fetch(self, progress):
        keys, page = [], 1
        while page <= 300:  # garde-fou
            d = self._call("/profile/owned-keys", page=page)
            batch = d.get("owned_keys") if isinstance(d, dict) else None
            if not isinstance(batch, list) or not batch:
                break
            keys += batch
            progress("itch.io : lecture de la bibliothèque", len(keys), 0)
            per_page = int(d.get("per_page") or 0)
            if len(batch) < per_page or not per_page:
                break
            page += 1
        games, seen = [], set()
        for k in keys:
            game = k.get("game") or {}
            gid, title = game.get("id"), (game.get("title") or "").strip()
            if not gid or not title or gid in seen:
                continue
            if game.get("classification") not in (None, "", "game"):  # bandes-son, outils, ressources…
                continue
            seen.add(gid)
            cover = next((u for u in (game.get("still_cover_url"), game.get("cover_url"))
                          if isinstance(u, str) and u.startswith("https://")), "")
            url = game.get("url") if isinstance(game.get("url"), str) and game["url"].startswith("https://") else ""
            games.append({"title": title, "skey": f"itchio:{gid}", "cover_base": cover,
                          "cover_urls": [cover] if cover else [], "link": url})
        return games


# ---- Plateformes à liste manuelle et/ou connexion (Ubisoft Connect, Prime Gaming)
class ListMixin:
    """Liste de jeux saisie à la main (« Titre | lien | image »), conservée dans la page HTML.
    Pour Ubisoft et Prime Gaming, elle sert de secours ou de complément à la connexion."""
    has_list = True
    help = ""

    def read_text(self):
        return MANUAL.get(self.id, "")

    def write_text(self, text):
        MANUAL[self.id] = text  # conservé dans la page HTML à la prochaine génération

    def parse(self):
        """Lignes « Titre | lien (facultatif) | image (facultative) »."""
        items, seen = [], set()
        for ln in self.read_text().splitlines():
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            parts = [p.strip() for p in ln.split("|")]
            title = parts[0]
            if not title or title.lower() in seen:
                continue
            seen.add(title.lower())
            link = parts[1] if len(parts) > 1 and parts[1].startswith("https://") else ""
            image = parts[2] if len(parts) > 2 and parts[2].startswith("https://") else ""
            items.append({"title": title, "link": link, "image": image})
        return items

    def count(self):
        return len(self.parse())

    def connected(self):
        """Connexion active (jetons présents) ; pour une liste seule : liste non vide."""
        return self.tokens_path.exists() if self.token_file else self.count() > 0

    def logged_in(self):
        return self.connected() or self.count() > 0

    def list_games(self, progress):
        items = self.parse()
        cache = CTX["lookup"]
        todo = [i for i in items if not i["image"] and norm_title(i["title"]) not in cache]
        done, lock = 0, threading.Lock()

        def lookup(i):
            nonlocal done
            key, appid = norm_title(i["title"]), steam_lookup(i["title"])  # jaquette via la recherche Steam
            with lock:
                done += 1
                progress(f"{self.name} : recherche des jaquettes", done, len(todo))
            return key, appid

        if todo:
            with ThreadPoolExecutor(max_workers=6) as ex:
                for key, appid in ex.map(lookup, todo):
                    if appid is not None:
                        cache[key] = appid

        games = []
        for i in items:
            if i["image"]:
                base, urls = i["image"], [i["image"]]
            elif cache.get(norm_title(i["title"])):
                base, urls = steam_cover_urls(cache[norm_title(i["title"])])
            else:
                base, urls = "", []
            games.append({"title": i["title"], "skey": f"{self.id}:{i['title'].lower()}",
                          "cover_base": base, "cover_urls": urls, "link": i["link"]})
        return games

    def fetch(self, progress):
        """Jeux de la connexion (si active) complétés par la liste manuelle (titres absents seulement)."""
        api = []
        self.src, self.last_warning = "list", ""
        if self.connected():
            try:
                api = self.api_games(progress)
                self.src = "api"
            except NotLoggedIn:
                if not self.count():
                    raise
                self.logout()
                detail = f" ({self.last_error})" if self.last_error else ""
                self.last_warning = f"{self.name} : session expirée, liste manuelle utilisée (reconnecte-toi){detail}."
        have = {norm_title(g["title"]) for g in api}
        extra = [g for g in (self.list_games(progress) if self.count() else [])
                 if norm_title(g["title"]) not in have]
        return api + extra


class ManualStore(ListMixin, Store):
    """Plateforme sans connexion possible : uniquement une liste saisie à la main."""
    kind = "manual"

    def logout(self):
        pass

    def check(self):
        n = self.count()
        return {"state": "ok", "user": f"{n} jeux"} if n else {"state": "none"}

    def fetch(self, progress):
        self.src = "list"
        return self.list_games(progress)


# ---- Prime Gaming / Amazon Games : même méthode que l'application « Amazon Games »
# (observée dans Lutris) : connexion Amazon, enregistrement d'un « appareil », lecture des droits d'accès.
AMZ_API = "https://api.amazon.com"
AMZ_ENTITLEMENTS = "https://gaming.amazon.com/api/distribution/entitlements"
AMZ_UA = "com.amazon.agslauncher.win/3.0.9202.1"
AMZ_DEVICE_TYPE = "A2UMVHOX7UP4V7"
AMZ_TARGET = "com.amazon.animusdistributionservice.entitlement.AnimusEntitlementsService.GetEntitlements"
AMZ_KEY_ID = "d5dc8b8b-86c8-4fc4-ae93-18c0def5314d"


def b64url(raw):
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


class PrimeStore(ListMixin, Store):
    id, name, tag, token_file = "prime", "Prime Gaming", "PRIME", "prime_tokens.json"
    kind = "oauth"
    placeholder = "https://www.amazon.com/?openid.oa2.authorization_code=…"
    steps = ["Clique sur le bouton et connecte-toi à ton compte Amazon (celui de Prime Gaming).",
             "Une page Amazon s'affiche ensuite : copie son adresse complète (Ctrl+L puis Ctrl+C). "
             "Elle doit contenir « openid.oa2.authorization_code ».",
             "Reviens ici et clique sur « Coller et valider » (ou Ctrl+V dans le champ). "
             "Le code expire vite et ne sert qu'une fois."]
    help = ("Liste de secours : un jeu par ligne (« Titre | lien | image », lien et image facultatifs). "
            "Elle complète la connexion ou la remplace si elle est indisponible, et elle est enregistrée "
            "dans la page HTML à la prochaine génération.")

    def __init__(self):
        super().__init__()
        self._pending = None  # secrets de la connexion en cours (PKCE), gardés en mémoire seulement

    def _pending_login(self):
        if self._pending is None:
            serial = uuid.uuid4().hex.upper()
            self._pending = {"verifier": b64url(secrets.token_bytes(32)), "serial": serial,
                             "client_id": f"{serial}#{AMZ_DEVICE_TYPE}".encode().hex()}
        return self._pending

    @property
    def auth_url(self):
        p = self._pending_login()
        challenge = b64url(hashlib.sha256(p["verifier"].encode()).digest())
        return "https://amazon.com/ap/signin?" + urlencode({
            "openid.ns": "http://specs.openid.net/auth/2.0",
            "openid.claimed_id": "http://specs.openid.net/auth/2.0/identifier_select",
            "openid.identity": "http://specs.openid.net/auth/2.0/identifier_select",
            "openid.mode": "checkid_setup",
            "openid.oa2.scope": "device_auth_access",
            "openid.ns.oa2": "http://www.amazon.com/ap/ext/oauth/2",
            "openid.oa2.response_type": "code",
            "openid.oa2.code_challenge_method": "S256",
            "openid.oa2.client_id": f"device:{p['client_id']}",
            "language": "en_US",
            "marketPlaceId": "ATVPDKIKX0DER",
            "openid.return_to": "https://www.amazon.com",
            "openid.pape.max_auth_age": 0,
            "openid.assoc_handle": "amzn_sonic_games_launcher",
            "pageId": "amzn_sonic_games_launcher",
            "openid.oa2.code_challenge": challenge})

    @staticmethod
    def extract_code(text):
        text = text.strip()
        if "openid.oa2.authorization_code" in text:
            q = parse_qs(urlparse(text).query)
            return (q.get("openid.oa2.authorization_code") or [""])[0]
        return text if re.fullmatch(r"[A-Za-z0-9_-]{16,}", text) else ""

    def login(self, text):
        code = self.extract_code(text)
        if not code:
            raise ValueError("Adresse non reconnue : elle doit contenir « openid.oa2.authorization_code ». "
                             "Copie l'adresse complète de la page Amazon affichée après ta connexion.")
        p = self._pending_login()
        body = {"auth_data": {"authorization_code": code, "client_domain": "DeviceLegacy",
                              "client_id": p["client_id"], "code_algorithm": "SHA-256",
                              "code_verifier": p["verifier"], "use_global_authentication": False},
                "registration_data": {"app_name": "AGSLauncher for Windows", "app_version": "1.0.0",
                                      "device_model": "Windows", "device_name": None,
                                      "device_serial": p["serial"], "device_type": AMZ_DEVICE_TYPE,
                                      "domain": "Device", "os_version": "10.0.19044.0"},
                "requested_extensions": ["customer_info", "device_info"],
                "requested_token_type": ["bearer", "mac_dms"], "user_context_map": {}}
        try:
            res = http_json("POST", AMZ_API + "/auth/register", body,
                            {"User-Agent": AMZ_UA, "Accept": "application/json", "Accept-Language": "en_US"})
        except urllib.error.HTTPError as e:
            raise ValueError(f"Connexion refusée par Amazon (HTTP {e.code}). Recommence la connexion : le code "
                             "expire vite, ne sert qu'une fois et doit venir du lien affiché par l'application. "
                             "Un compte d'une autre région qu'amazon.com peut aussi être refusé.") from e
        except urllib.error.URLError as e:
            raise ValueError("Connexion impossible : " + net_error(e, "Amazon")) from e
        ok = (res.get("response") or {}).get("success")
        if not ok or "tokens" not in ok:
            raise ValueError("Réponse inattendue d'Amazon : la connexion n'a pas abouti.")
        bearer, ext = ok["tokens"]["bearer"], ok.get("extensions") or {}
        write_private(self.tokens_path, {
            "access_token": bearer["access_token"], "refresh_token": bearer["refresh_token"],
            "expires_at": time.time() + int(bearer.get("expires_in", 3600)),
            "serial": (ext.get("device_info") or {}).get("device_serial_number") or p["serial"],
            "name": (ext.get("customer_info") or {}).get("name", "")})
        self._pending = None

    def _refresh(self, refresh_token):
        r = http_json("POST", AMZ_API + "/auth/token", {
            "source_token": refresh_token, "source_token_type": "refresh_token",
            "requested_token_type": "access_token", "app_name": "AGSLauncher for Windows",
            "app_version": "1.0.0"}, {"User-Agent": AMZ_UA, "Accept": "application/json",
                                      "Accept-Language": "en_US"})
        t = json.loads(self.tokens_path.read_text("utf-8"))
        t["access_token"] = r["access_token"]
        t["expires_at"] = time.time() + int(r.get("expires_in", 3600))
        write_private(self.tokens_path, t)

    def verify(self):
        token = self.access_token()
        try:
            d = http_json("GET", AMZ_API + "/user/profile", None,
                          {"Authorization": "bearer " + token, "User-Agent": AMZ_UA, "Accept": "application/json"})
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise NotLoggedIn() from e
            raise
        return d.get("name", "") if isinstance(d, dict) else ""

    def api_games(self, progress):
        token = self.access_token()
        serial = json.loads(self.tokens_path.read_text("utf-8"))["serial"]
        headers = {"X-Amz-Target": AMZ_TARGET, "x-amzn-token": token, "User-Agent": AMZ_UA,
                   "Content-Type": "application/json", "Content-Encoding": "amz-1.0"}
        by_asin, next_token, total = defaultdict(list), None, 0
        while True:
            body = {"Operation": "GetEntitlements", "clientId": "Sonic", "syncPoint": None,
                    "nextToken": next_token, "maxResults": 50, "productIdFilter": None,
                    "keyId": AMZ_KEY_ID, "hardwareHash": hashlib.sha256(serial.encode()).hexdigest().upper()}
            try:
                d = http_json("POST", AMZ_ENTITLEMENTS, body, headers)
            except urllib.error.HTTPError as e:
                if e.code in (401, 403):
                    raise NotLoggedIn() from e
                raise
            for ent in d.get("entitlements", []):
                product = ent.get("product") or {}
                if "id" in product and product.get("title"):
                    by_asin[product.get("asin") or ""].append(ent)
                    total += 1
            progress("Prime Gaming : lecture de la bibliothèque", total, 0)
            next_token = d.get("nextToken")
            if not next_token:
                break
        # un même jeu peut avoir plusieurs droits : un seul par ASIN (le plus ancien identifiant)
        no_asin = by_asin.pop("", [])
        chosen = no_asin + [sorted(g, key=lambda x: str(x.get("id")))[0] for g in by_asin.values()]
        games = []
        for ent in chosen:
            product = ent["product"]
            det = (product.get("productDetail") or {}).get("details") or {}
            urls = [det[k] for k in ("logoUrl", "iconUrl", "backgroundUrl1", "backgroundUrl2")
                    if isinstance(det.get(k), str) and det[k].startswith("https://")]
            games.append({"title": product["title"], "skey": f"prime:{ent.get('id') or product['id']}",
                          "cover_base": urls[0] if urls else "", "cover_urls": urls, "link": ""})
        return games


# ---- Ubisoft Connect : session de connect.ubisoft.com (jetons du navigateur) + API de la bibliothèque,
# comme dans Lutris. Les jetons de session sont copiés depuis le navigateur avec un petit script.
UBI_APPID = "82b650c0-6cb3-40c0-9f41-25a53b62b206"
UBI_GENOME = "42d07c95-9914-4450-8b38-267c4e462b21"
UBI_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
          "Chrome/72.0.3626.121 Safari/537.36")
UBI_SESSIONS = "https://public-ubiservices.ubi.com/v3/profiles/sessions"
UBI_SESSIONS_V2 = "https://public-ubiservices.ubi.com/v2/profiles/sessions"
UBI_GRAPHQL = "https://public-ubiservices.ubi.com/v1/profiles/me/uplay/graphql"
UBI_QUERY = ("query AllGames { viewer { id ...ownedGamesList } } "
             "fragment gameProps on Game { id spaceId name coverUrl backgroundUrl bannerUrl } "
             "fragment ownedGameProps on Game { ...gameProps viewer { meta { id "
             "ownedPlatformGroups { id name type } } } } "
             "fragment ownedGamesList on User { ownedGames: games(filterBy: {isOwned: true}) "
             "{ totalCount nodes { ...ownedGameProps } } }")


def parse_iso(text):
    """Date d'Ubisoft (ex. 2026-11-02T10:00:00.1234567Z) -> datetime ; None si illisible."""
    m = re.match(r"(\d{4}-\d{2}-\d{2})T(\d{2}:\d{2}:\d{2})(?:\.(\d+))?", str(text or ""))
    if not m:
        return None
    frac = (m.group(3) or "0")[:6].ljust(6, "0")
    return datetime.strptime(f"{m.group(1)}T{m.group(2)}.{frac}", "%Y-%m-%dT%H:%M:%S.%f")


class UbisoftStore(ListMixin, Store):
    id, name, tag, token_file = "ubisoft", "Ubisoft Connect", "UBI", "ubisoft_tokens.json"
    kind = "paste"
    auth_url = ("https://connect.ubisoft.com/login?appId=" + UBI_APPID + "&genomeId=" + UBI_GENOME
                + "&lang=en-US&nextUrl=https%3A%2F%2Fconnect.ubisoft.com%2Fready")
    snippet = ('(()=>{const e=[],r=["PRODloginData","PRODrememberMe","PRODlastProfile"].map(k=>{'
               'for(const s of ["localStorage","sessionStorage"]){try{const v=window[s].getItem(k);if(v)return v}'
               'catch(x){e.push(s+": "+(x.name||x))}}return null});'
               'copy(JSON.stringify(e.length?[...r,{_errors:[...new Set(e)]}]:r))})()')
    placeholder = '["{\\"ticket\\":…}", …]'
    extra_links = [{"label": "Ouvrir la page de lecture de la session",
                    "url": "https://connect.ubisoft.com/change_domain/"}]
    steps = ["Clique sur « Ouvrir la connexion » et connecte-toi (coche « Se souvenir de moi »). "
             "Une page 404 s'affiche ensuite : c'est normal.",
             "Clique sur « Ouvrir la page de lecture de la session ».",
             "Sur cette page, appuie sur F12, ouvre l'onglet « Console », colle le script ci-dessous et valide "
             "(si le navigateur le demande, écris d'abord « allow pasting »).",
             "Reviens ici et clique sur « Coller et valider ». Ce que tu copies contient ta session : ne le "
             "partage avec personne."]
    alt_title = "Ça ne marche pas ? Autre méthode (onglet Réseau)"
    alt_steps = ["Ouvre les outils du navigateur (touche F12) puis l'onglet « Réseau » et active « Conserver les "
                 "journaux » (Firefox : roue dentée ; Chrome : « Preserve log »). Fais-le avant de te connecter.",
                 "Clique sur « Ouvrir la connexion » et connecte-toi (coche « Se souvenir de moi »).",
                 "Dans le Réseau, tape « sessions » dans le filtre. Choisis la dernière ligne dont le domaine est "
                 "« https://public-ubiservices.ubi.com » et le fichier est « sessions » (adresse complète : "
                 "https://public-ubiservices.ubi.com/v3/profiles/sessions). Si tu as un code de double "
                 "authentification, prends la dernière ligne.",
                 "Clique sur cette ligne, ouvre l'onglet « Réponse », fais un clic droit puis « Tout copier » "
                 "(pas « Copier la valeur »).",
                 "Reviens ici, colle dans le champ et clique sur « Coller et valider ». Ce que tu copies contient "
                 "ta session : ne le partage avec personne."]
    help = ("Liste de secours : un jeu par ligne (« Titre | lien | image », lien et image facultatifs). "
            "Elle complète la connexion ou la remplace si elle est indisponible, et elle est enregistrée "
            "dans la page HTML à la prochaine génération.")

    @staticmethod
    def parse_storage(text):
        """Fusionne les JSON copiés depuis le navigateur : liste de 3 chaînes JSON, ou format « a,b,c »."""
        text = text.strip()
        try:
            data = json.loads(text)
            objs = data if isinstance(data, list) else [data]
        except ValueError:
            try:
                objs = json.loads("[" + text + "]")
            except ValueError:
                raise ValueError("Texte non reconnu : colle ce que tu as copié depuis le navigateur.")
        errs = [str(e) for o in objs if isinstance(o, dict) for e in (o.get("_errors") or [])]
        objs = [o for o in objs if not (isinstance(o, dict) and "_errors" in o)]
        hint = (" Ton navigateur bloque l'accès au stockage (" + ", ".join(errs) + ") : utilise plutôt l'autre "
                "méthode (onglet Réseau), décrite sous les étapes.") if errs else ""
        if objs and all(o in (None, "", "null") for o in objs):
            raise ValueError("Le script n'a rien trouvé. Lance-le sur https://connect.ubisoft.com/change_domain/ "
                             "juste après ta connexion, ou utilise l'autre méthode (onglet Réseau)." + hint)
        if any(isinstance(o, dict) and o.get("twoFactorAuthenticationTicket") and not o.get("ticket") for o in objs):
            raise ValueError("C'est l'étape du code de double authentification : choisis la ligne suivante, "
                             "celle dont la réponse contient « ticket ».")
        creds = {}
        for o in objs:
            if isinstance(o, str):
                try:
                    o = json.loads(o)
                except ValueError:
                    continue
            if isinstance(o, dict):
                for k in ("userId", "nameOnPlatform", "ticket", "rememberMeTicket", "sessionId"):
                    if o.get(k):
                        creds[k] = o[k]
        if not all(creds.get(k) for k in ("userId", "ticket", "sessionId")):
            raise ValueError("Informations incomplètes : reconnecte-toi, puis recopie-les depuis la bonne page "
                             "ou avec l'autre méthode (onglet Réseau)." + hint)
        creds["username"] = creds.pop("nameOnPlatform", "")
        return creds

    def _creds(self):
        if not self.tokens_path.exists():
            raise NotLoggedIn()
        return json.loads(self.tokens_path.read_text("utf-8"))

    @staticmethod
    def _headers(c, auth=None, refresh=False):
        """En-têtes comme dans Lutris : appels normaux = session ; renouvellements = navigateur de connect."""
        h = {"Ubi-AppId": UBI_APPID, "User-Agent": UBI_UA, "Accept": "*/*",
             "Authorization": auth or f"Ubi_v1 t={c['ticket']}"}
        if refresh:
            h.update({"Origin": "https://connect.ubisoft.com", "Referer": "https://connect.ubisoft.com",
                      "Content-Type": "application/json", "Accept-Language": "en-US;en;q=0.5"})
        elif c.get("sessionId"):
            h["Ubi-SessionId"] = c["sessionId"]
        return h

    @staticmethod
    def _describe(e):
        """Texte lisible d'une erreur d'Ubisoft : code HTTP + message du serveur."""
        detail = ""
        try:
            d = json.loads(e.read() or b"{}")
            if d.get("message"):
                detail = f"{d['message']} (errorCode {d.get('errorCode', '?')})"
        except Exception:
            detail = str(getattr(e, "msg", "") or "")
        return f"HTTP {e.code}" + (f" : {detail}" if detail and detail != "None" else "")

    def _note(self, text):
        self.last_error = (self.last_error + " ; " if self.last_error else "") + text

    @staticmethod
    def _stamp(c, j):
        """Heure à laquelle la session doit être renouvelée (d'après « expiration » et « serverTime »)."""
        if isinstance(j, dict):
            exp, srv = parse_iso(j.get("expiration")), parse_iso(j.get("serverTime"))
            if exp and srv:
                c["refreshTime"] = time.time() + (exp - srv).total_seconds()

    def _renew(self, c):
        """Renouvelle le ticket (ou, à défaut, avec le jeton « se souvenir de moi »)."""
        def apply(j):
            c["ticket"], c["sessionId"] = j["ticket"], j["sessionId"]
            c["userId"] = j.get("userId", c.get("userId"))
            if j.get("username"):
                c["username"] = j["username"]
            if j.get("rememberMeTicket"):
                c["rememberMeTicket"] = j["rememberMeTicket"]
            self._stamp(c, j)
        try:
            j = http_json("PUT", UBI_SESSIONS, None, self._headers(c, refresh=True))
        except urllib.error.HTTPError as e1:
            self._note("renouvellement du ticket refusé (" + self._describe(e1) + ")")
            remember = c.get("rememberMeTicket")
            if not remember:
                self._note("pas de jeton « se souvenir de moi »")
                raise NotLoggedIn()
            try:
                apply(http_json("POST", UBI_SESSIONS, {"rememberMe": True},
                                self._headers(c, f"rm_v1 t={remember}", refresh=True)))
                j = http_json("PUT", UBI_SESSIONS, None, self._headers(c, refresh=True))
            except urllib.error.HTTPError as e2:
                self._note("jeton « se souvenir de moi » refusé (" + self._describe(e2) + ")")
                raise NotLoggedIn() from e2
        if not isinstance(j, dict) or "ticket" not in j:
            self._note("réponse de renouvellement inattendue")
            raise NotLoggedIn()
        apply(j)
        write_private(self.tokens_path, c)

    def _call(self, c, method, url, obj=None, json_header=False):
        """Requête authentifiée : renouvellement avant l'expiration, puis une tentative après un refus."""
        self.last_error = ""
        if c.get("refreshTime") and time.time() > float(c["refreshTime"]) - 120:
            self._renew(c)

        def once():
            h = self._headers(c)
            if json_header:
                h["Content-Type"] = "application/json"
            d = http_json(method, url, obj, h)
            if isinstance(d, dict) and d.get("errorCode") and d.get("message"):
                raise urllib.error.HTTPError(url, int(d.get("httpCode") or 401), str(d["message"]), {}, None)
            return d
        try:
            return once()
        except urllib.error.HTTPError as e:
            if e.code not in (401, 403, 412):
                raise
            self._note("requête refusée (" + self._describe(e) + ")")
        self._renew(c)
        try:
            return once()
        except urllib.error.HTTPError as e:
            if e.code in (401, 403, 412):
                self._note("encore refusée après renouvellement (" + self._describe(e) + ")")
                raise NotLoggedIn() from e
            raise

    def login(self, text):
        creds = self.parse_storage(text)
        write_private(self.tokens_path, creds)
        try:
            self.verify()
        except NotLoggedIn:
            err = self.last_error
            self.logout()
            raise ValueError("Ubisoft a refusé la session" + (f" ({err})" if err else "")
                             + ". Reconnecte-toi, puis recopie vite les informations : elles expirent en "
                             "quelques heures.")
        except Exception as e:
            self.logout()
            raise ValueError("Vérification impossible : " + describe(e, "Ubisoft")) from e

    def verify(self):
        c = self._creds()
        d = self._call(c, "POST", UBI_SESSIONS_V2, None, json_header=True)  # confirmation de la session, comme Lutris
        self._stamp(c, d)
        write_private(self.tokens_path, c)
        name = (d.get("nameOnPlatform") if isinstance(d, dict) else "") or c.get("username", "")
        return name + ("" if c.get("rememberMeTicket") else " — session courte, sans « se souvenir de moi »")

    def api_games(self, progress):
        c = self._creds()
        d = self._call(c, "POST", UBI_GRAPHQL, {"operationName": "AllGames", "variables": {"owned": True},
                                                 "query": UBI_QUERY})
        nodes = (((d.get("data") or {}).get("viewer") or {}).get("ownedGames") or {}).get("nodes") or []
        progress("Ubisoft Connect : lecture de la bibliothèque", len(nodes), len(nodes))
        games, seen = [], set()
        for n in nodes:
            name, gid = (n.get("name") or "").strip(), n.get("spaceId") or n.get("id")
            if not name or not gid or gid in seen:
                continue
            groups = ((n.get("viewer") or {}).get("meta") or {}).get("ownedPlatformGroups") or []
            types = [p.get("type") for grp in groups for p in (grp if isinstance(grp, list) else [grp])
                     if isinstance(p, dict)]
            if types and "PC" not in types:  # jeu possédé seulement sur console
                continue
            seen.add(gid)
            cover = next((u for u in (n.get("coverUrl"), n.get("bannerUrl"))
                          if isinstance(u, str) and u.startswith("https://")), "")
            games.append({"title": name, "skey": f"ubisoft:{gid}", "cover_base": cover,
                          "cover_urls": [cover] if cover else [], "link": ""})
        return games


# ---- SteamGridDB (service d'images, facultatif) : jaquettes verticales « Grids »
SGDB_PARAMS = {"dimensions": "600x900,342x482,660x930", "types": "static", "nsfw": "false"}


class GridService(Store):
    id, name, tag, token_file = ("steamgriddb", "SteamGridDB (visuels, facultatif)", "SGDB",
                                 "steamgriddb.json")
    kind, service = "key", True
    auth_url = "https://www.steamgriddb.com/profile/preferences/api"
    fields = [{"name": "key", "label": "Clé API SteamGridDB", "secret": True}]
    steps = ["Crée un compte gratuit sur steamgriddb.com, puis ouvre Préférences > API "
             "(bouton ci-dessous).",
             "Génère ta clé API et copie-la.",
             "Colle-la ci-dessous : les jaquettes « Grids » de SteamGridDB seront utilisées en "
             "priorité, à la place de celles des boutiques."]

    def _key(self):
        if not self.tokens_path.exists():
            raise NotLoggedIn()
        return json.loads(self.tokens_path.read_text("utf-8"))["api_key"]

    def _call(self, path, **params):
        url = SGDB_API + path + ("?" + urlencode(params) if params else "")
        for attempt in (0, 1):
            try:
                return json.loads(http_get(url, {"Authorization": "Bearer " + self._key()}))
            except urllib.error.HTTPError as e:
                if e.code in (401, 403):
                    raise NotLoggedIn() from e
                if e.code == 429 and attempt == 0:  # trop de requêtes : une seconde chance
                    time.sleep(2)
                    continue
                raise

    def login_fields(self, v):
        key = (v.get("key") or "").strip()
        if not re.fullmatch(r"[0-9A-Za-z]{20,64}", key):
            raise ValueError("Clé API non reconnue (20 à 64 caractères, lettres et chiffres).")
        write_private(self.tokens_path, {"api_key": key})
        try:
            self.verify()
        except NotLoggedIn:
            self.logout()
            raise ValueError("Clé API refusée par SteamGridDB.")
        except Exception as e:
            self.logout()
            raise ValueError("Vérification impossible : " + describe(e, "SteamGridDB")) from e

    def verify(self):
        self._call("/search/autocomplete/portal")
        return ""

    def find_thumb(self, entry):
        """Miniature de la meilleure grille verticale du jeu (None : aucun résultat)."""
        items = []
        steam = next((g for g in entry["games"] if g["skey"].startswith("steam:")), None)
        if steam:  # identifiant Steam connu : correspondance exacte
            d = self._call("/grids/steam/" + steam["skey"].split(":", 1)[1], **SGDB_PARAMS)
            items = d.get("data") or []
        if not items:
            title = entry["title"]
            key = norm_title(title)
            found = (self._call("/search/autocomplete/" + quote(title, safe=""))).get("data") or []
            hit = next((r for r in found if norm_title(r.get("name", "")) == key), None)
            if not hit and found:
                best = max(found, key=lambda r: difflib.SequenceMatcher(
                    None, key, norm_title(r.get("name", ""))).ratio())
                if difflib.SequenceMatcher(None, key, norm_title(best.get("name", ""))).ratio() >= 0.88:
                    hit = best
            if hit:
                items = (self._call(f"/grids/game/{hit['id']}", **SGDB_PARAMS)).get("data") or []
        items = [i for i in items if i.get("thumb") or i.get("url")]
        if not items:
            return None
        top = max(items, key=lambda i: i.get("score") or 0)
        return top.get("thumb") or top.get("url")


STORES = [GOGStore(), EpicStore(), SteamStore(), UbisoftStore(), PrimeStore(), ItchStore()]
SGDB = GridService()
SERVICES = [SGDB]


def get_store(store_id):
    return next(s for s in STORES + SERVICES if s.id == store_id)


# ------------------------------------------------------------------- génération
def rescale_uri(uri, width, quality):
    """Réduit une image déjà intégrée (data URI) sans rien retélécharger ("" en cas d'échec)."""
    try:
        data = base64.b64decode(uri.split(",", 1)[1])
    except (IndexError, ValueError):
        return ""
    return process_image(data, width, quality)


def store_cover(entry, width, quality):
    """Jaquette fournie par la boutique, réduite en data URI ("" si introuvable)."""
    for g in entry["games"]:
        for url in g.get("cover_urls", []):
            try:
                data = http_get(url, timeout=25)
            except Exception:
                continue
            uri = process_image(data, width, quality) if data else ""
            if uri:
                return uri
    return ""


def norm_title(title):
    """Forme normalisée d'un titre, pour reconnaître un même jeu sur deux boutiques."""
    t = re.sub(r"[™®©]", "", title)
    t = unicodedata.normalize("NFKD", t)
    t = "".join(c for c in t if not unicodedata.combining(c)).lower().replace("&", " and ")
    t = re.sub(r"\b(?:game of the year|goty|definitive|complete|enhanced|deluxe|standard|"
               r"special|ultimate|gold|premium|anniversary|digital)\s+(?:edition|version)\b", " ", t)
    t = re.sub(r"[^a-z0-9]+", " ", t).strip()
    return re.sub(r"^the ", "", t)


def load_overrides():
    """Fusions manuelles : ~/.config/gog-bibliotheque/fusions.json
    {"Titre sur une boutique": "Titre sur l'autre"} (voir README du message)."""
    try:
        raw = json.loads((CONFIG / "fusions.json").read_text("utf-8"))
        return {norm_title(k): norm_title(v) for k, v in raw.items()}
    except (OSError, ValueError, AttributeError):
        return {}


def build_entries(games, overrides=None):
    """Une entrée par jeu : fusionne les titres identiques, entre boutiques
    (GOG + Epic) comme au sein d'une même boutique (plusieurs identifiants Epic)."""
    overrides = overrides or {}
    order = {s.id: i for i, s in enumerate(STORES)}
    groups = {}
    for g in sorted(games, key=lambda x: (x["title"].lower(), order.get(x["store"], 99))):
        k = norm_title(g["title"])
        k = overrides.get(k, k)
        e = groups.setdefault(k, {"games": [], "stores": []})
        e["games"].append(g)
        if g["store"] not in e["stores"]:
            e["stores"].append(g["store"])
    entries = list(groups.values())
    for e in entries:
        # Boutique prioritaire d'abord, puis titre le plus court (jeu de base).
        e["games"].sort(key=lambda x: (order.get(x["store"], 99), len(x["title"])))
        e["stores"].sort(key=lambda sid: order.get(sid, 99))
        e["title"] = e["games"][0]["title"]
    entries.sort(key=lambda e: e["title"].lower())
    return entries


PAGE = """<!DOCTYPE html>
<html lang="fr"><head><meta charset="utf-8">
<meta name="generator" content="gog_library __VERSION__">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Ma bibliothèque de jeux</title>
<style>
:root{--bg:#14141a;--fg:#eee;--card:#1f1f28;--muted:#9a9aa8;--accent:#e8a23a}
@media(prefers-color-scheme:light){:root{--bg:#f4f4f7;--fg:#1b1b22;--card:#fff;--muted:#666;--accent:#c77d00}}
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,sans-serif;background:var(--bg);color:var(--fg)}
header{position:sticky;top:0;z-index:5;background:var(--bg);padding:14px 20px;display:flex;gap:16px;align-items:center;flex-wrap:wrap;border-bottom:1px solid #8884}
h1{margin:0;font-size:1.2rem}#count{color:var(--muted);font-size:.9rem}
header label{font-size:.9rem;cursor:pointer}
#q{flex:1;min-width:180px;max-width:360px;padding:8px 12px;border-radius:8px;border:1px solid #8886;background:var(--card);color:var(--fg);font-size:1rem}
.chips{display:flex;gap:6px;flex-wrap:wrap}
.chip{background:transparent;color:var(--fg);border:1px solid #8886;border-radius:999px;padding:5px 12px;font-size:.85rem;cursor:pointer}
.chip.on{background:var(--accent);color:#111;border-color:var(--accent);font-weight:600}
main{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:16px;padding:20px}
.card{position:relative;margin:0;background:var(--card);border-radius:8px;overflow:hidden;box-shadow:0 2px 8px #0003;transition:transform .15s}
.card:hover{transform:translateY(-3px)}
.lnk{display:block;color:inherit;text-decoration:none}
.lnk:hover figcaption{color:var(--accent)}
.card img{width:100%;display:block;aspect-ratio:2/3;object-fit:cover}
.noimg{aspect-ratio:2/3;display:flex;align-items:center;justify-content:center;padding:10px;text-align:center;color:var(--muted)}
figcaption{padding:8px 10px;font-size:.82rem;line-height:1.25}
.badge{position:absolute;top:8px;left:8px;z-index:1;background:var(--accent);color:#111;font-size:.7rem;font-weight:700;padding:2px 8px;border-radius:999px;text-transform:uppercase}
.tags{position:absolute;top:8px;right:8px;z-index:1;display:flex;flex-direction:column;gap:3px;align-items:flex-end}
.tag{background:#000a;color:#fff;font-size:.62rem;font-weight:700;padding:2px 7px;border-radius:999px;letter-spacing:.04em}
.tag.gog{background:#6b3fd4e6}.tag.epic{background:#2a2a2ae6}.tag.steam{background:#1b6fa8e6}.tag.ubisoft{background:#0b63cee6}.tag.prime{background:#007da8e6}.tag.itchio{background:#e0463ee6}
.dlg{position:fixed;inset:0;z-index:20;background:#000a;display:flex;align-items:center;justify-content:center;padding:20px}
.dlg .box{background:var(--card);border-radius:12px;padding:20px;max-width:360px;width:100%;text-align:center}
.dlg h3{margin:0 0 14px;font-size:1rem}
.opt{display:block;background:var(--accent);color:#111;font-weight:600;text-decoration:none;border-radius:8px;padding:10px;margin-bottom:10px}
.dlg p{margin:8px 0;line-height:1.4}
.hidden{display:none!important}
</style></head><body>
<header><h1>Ma bibliothèque de jeux</h1><span id="count">__N__ jeux</span>
<input id="q" type="search" placeholder="Rechercher un jeu…" autofocus>__CHIPS____FILTER__</header>
<main>__CARDS__</main>
<div id="dlg" class="dlg hidden"><div class="box"><h3 id="dt"></h3><div id="dll"></div>
<button id="dx" class="chip">Annuler</button></div></div>
<div id="dlg2" class="dlg hidden"><div class="box"><h3 id="d2t"></h3>
<p>Boutique d'origine : <b id="d2o"></b></p><p id="d2m"></p>
<p>Redirection dans <b id="d2c">5</b> s…</p>
<a id="d2go" class="opt" href="#" rel="noopener noreferrer">Aller sur Steam maintenant</a>
<button id="d2x" class="chip">Annuler</button></div></div>
<script type="application/json" id="gl-data">__STATE__</script>
<script>
const cards=[...document.querySelectorAll('.card')],count=document.getElementById('count'),
q=document.getElementById('q'),onlyNew=document.getElementById('onlynew');
let store='';
function apply(){const s=q.value.trim().toLowerCase();let n=0;
for(const c of cards){const ss=c.dataset.s.split(' ');
const okStore=!store||(store==='*'?ss.length>1:ss.includes(store));
const show=(!s||c.dataset.t.includes(s))&&okStore&&(!onlyNew||!onlyNew.checked||c.classList.contains('new'));
c.classList.toggle('hidden',!show);if(show)n++}
count.textContent=n+' jeu'+(n>1?'x':'')}
q.addEventListener('input',apply);if(onlyNew)onlyNew.addEventListener('change',apply);
document.querySelectorAll('.chip[data-s]').forEach(b=>b.addEventListener('click',()=>{
document.querySelectorAll('.chip[data-s]').forEach(x=>x.classList.remove('on'));b.classList.add('on');
store=b.dataset.s;apply()}));
const dlg=document.getElementById('dlg'),dt=document.getElementById('dt'),dll=document.getElementById('dll');
document.querySelectorAll('a.pick').forEach(a=>a.addEventListener('click',ev=>{
ev.preventDefault();dt.textContent=a.dataset.title;dll.innerHTML='';
JSON.parse(a.dataset.links).forEach(l=>{if(!/^https:\\/\\//.test(l.u))return;
const b=document.createElement('a');b.className='opt';b.href=l.u;b.target='_blank';b.rel='noopener noreferrer';
b.textContent='Ouvrir sur '+l.n;b.addEventListener('click',()=>dlg.classList.add('hidden'));dll.appendChild(b)});
dlg.classList.remove('hidden')}));
dlg.addEventListener('click',e=>{if(e.target===dlg||e.target.id==='dx')dlg.classList.add('hidden')});
const d2=document.getElementById('dlg2');let t2=null;
function closeD2(){clearInterval(t2);t2=null;d2.classList.add('hidden')}
document.querySelectorAll('a.steamfb').forEach(a=>a.addEventListener('click',ev=>{
ev.preventDefault();const url=a.href;if(!/^https:\\/\\/store\\.steampowered\\.com\\//.test(url))return;
document.getElementById('d2t').textContent=a.dataset.title;
document.getElementById('d2o').textContent=a.dataset.origin;
document.getElementById('d2m').textContent="Cette boutique ne propose pas de page pour ce jeu. Vous allez être redirigé vers "+(a.dataset.exact==='1'?"sa page":"la recherche")+" Steam.";
let n=5;const c=document.getElementById('d2c');c.textContent=n;document.getElementById('d2go').href=url;
d2.classList.remove('hidden');clearInterval(t2);
t2=setInterval(()=>{n--;c.textContent=n;if(n<=0){clearInterval(t2);location.href=url}},1000)}));
document.getElementById('d2x').addEventListener('click',closeD2);
d2.addEventListener('click',e=>{if(e.target===d2)closeD2()});
document.addEventListener('keydown',e=>{if(e.key==='Escape'){dlg.classList.add('hidden');closeD2()}});
</script></body></html>"""


def parse_previous(text):
    """Lit une page générée précédemment : jeux déjà connus (avec leur date d'ajout), jaquettes,
    caches et listes manuelles. Remplace toute base de données locale."""
    prev = {"ok": False, "legacy": False, "seen": {}, "init": set(), "covers": {}, "epic": {},
            "lookup": {}, "manual": {}, "srcs": {}, "miss": set(), "width": 0, "titles": set(),
            "date": "", "count": 0}
    if not text:
        return prev
    m = re.search(r'<script type="application/json" id="gl-data">(.*?)</script>', text, re.S)
    if m:
        try:
            st = json.loads(m.group(1))
            prev.update(seen=dict(st.get("seen", {})), init=set(st.get("init", [])),
                        epic=dict(st.get("epic", {})), lookup=dict(st.get("lookup", {})),
                        manual=dict(st.get("manual", {})), srcs=dict(st.get("srcs", {})),
                        miss=set(st.get("miss", [])),
                        width=int(st.get("width", 0)), date=str(st.get("date", "")), ok=True)
        except (ValueError, TypeError, AttributeError):
            pass
    for fm in re.finditer(r'<figure class="card[^"]*" data-s="[^"]*" data-k="([^"]*)" '
                          r'data-c="([^"]*)"[^>]*>(.*?)</figure>', text, re.S):
        prev["count"] += 1
        try:
            keys = json.loads(html.unescape(fm.group(1)))
        except ValueError:
            continue
        im = re.search(r'<img src="(data:[^"]+)"', fm.group(3))
        if im:
            for k in keys:
                prev["covers"][k] = (im.group(1), fm.group(2), prev["width"])
    if not prev["ok"]:  # page d'une ancienne version : on ne retrouve les jeux que par leur titre
        titles = re.findall(r"<figcaption>(.*?)</figcaption>", text, re.S)
        if titles:
            prev.update(ok=True, legacy=True, count=len(titles),
                        titles={norm_title(html.unescape(t)) for t in titles})
    return prev


def seed_manual(prev=None):
    """Reprend les listes manuelles de l'ancienne page (ou, à défaut, d'anciens fichiers jeux_*.txt)."""
    for sid, txt in ((prev or {}).get("manual") or {}).items():
        MANUAL.setdefault(sid, txt)
    for s in STORES:
        if s.has_list and s.id not in MANUAL:
            try:
                MANUAL[s.id] = (CONFIG / f"jeux_{s.id}.txt").read_text("utf-8")
            except OSError:
                pass


def previous_candidates(out):
    """Pages déjà générées : la page unique et les pages par plateforme (même dossier)."""
    out = Path(out)
    paths = [out] + [out.with_name(f"{out.stem}_{s.id}{out.suffix}") for s in STORES]
    return [p for p in paths if p.is_file()]


def previous_signature(out):
    sig = []
    for p in previous_candidates(out):
        st = p.stat()
        sig.append((p.name, st.st_mtime, st.st_size))
    return tuple(sig)


def merge_previous(parts):
    """Réunit l'historique et les images de plusieurs pages (la plus récente prime)."""
    parts = sorted(parts, key=lambda p: -p.get("mtime", 0))
    modern = [p for p in parts if not p["legacy"]]
    use = modern or parts
    m = parse_previous("")
    if not use:
        return m
    m.update(ok=True, legacy=not modern, width=use[0]["width"], date=use[0]["date"],
             files=[p.get("file", "") for p in use])
    for p in use:
        for key in ("seen", "covers", "epic", "lookup", "manual", "srcs"):
            for k, v in p[key].items():
                m[key].setdefault(k, v)
        m["init"] |= p["init"]
        m["miss"] |= p["miss"]
        m["titles"] |= p["titles"]
    m["count"] = len(m["titles"]) if m["legacy"] else len(m["seen"])
    return m


def load_previous_set(out):
    parts = []
    for p in previous_candidates(out):
        try:
            pp = parse_previous(p.read_text("utf-8", errors="ignore"))
        except OSError:
            continue
        if pp["ok"]:
            pp["file"], pp["mtime"] = p.name, p.stat().st_mtime
            parts.append(pp)
    return merge_previous(parts)


def sid_of(key):
    return key.split(":", 1)[0]


def generate(progress=lambda *a: None, out=None, previous=None, preset="standard", refresh=False,
             single=True, per_platform=False):
    """Lit les plateformes connectées, prépare les jaquettes réduites (base64) et écrit les pages.
    single       : une page unique avec toutes les plateformes ;
    per_platform : une page par plateforme (les deux options peuvent être cumulées).
    previous : texte d'une ancienne page (par défaut : les pages déjà présentes à côté du fichier de sortie)."""
    out = Path(out or OUTPUT)
    width, quality = PRESETS.get(preset, PRESETS["standard"])
    if not (single or per_platform):
        raise ValueError("Choisis au moins un type de fichier (unique ou par plateforme).")
    prev = load_previous_set(out) if previous is None else parse_previous(previous)
    seed_manual(prev)
    CTX.update(epic=dict(prev["epic"]), epic_seen=set(), lookup=dict(prev["lookup"]), noshrink=False)

    logged = [s for s in STORES if s.logged_in()]
    if not logged:
        raise NotLoggedIn()
    connected = logged

    games, ok_stores, warnings = [], [], []
    for s in connected:
        try:
            lst = s.fetch(progress)
        except NotLoggedIn:
            s.logout()
            detail = f" ({s.last_error})" if s.last_error else ""
            warnings.append(f"{s.name} : session expirée, reconnecte-toi{detail} (ignoré cette fois).")
            continue
        except Exception as e:
            warnings.append(f"{s.name} : {describe(e, s.name)} (ignoré cette fois).")
            continue
        for g in lst:
            g["store"] = s.id
        games += lst
        ok_stores.append(s)
        if getattr(s, "last_warning", ""):
            warnings.append(s.last_warning)
    if not ok_stores:
        raise RuntimeError(" ".join(warnings))
    games.sort(key=lambda g: g["title"].lower())

    # Nouveautés : comparaison avec les anciennes pages (aucun fichier sur le disque).
    today = date.today().isoformat()
    limit = (date.today() - timedelta(days=BADGE_DAYS)).isoformat()
    multi_all = len(ok_stores) > 1
    seen, added = {}, []
    for s in ok_stores:
        initialized = prev["ok"] and (prev["legacy"] or s.id in prev["init"])
        if initialized and s.has_list and prev["srcs"].get(s.id, "list") != getattr(s, "src", "list"):
            initialized = False  # passage de la liste à la connexion (ou inversement) : pas de faux « Nouveau »
        old_titles = ({norm_title(k.split(":", 1)[1]) for k in prev["seen"] if k.startswith(s.id + ":")}
                      if s.has_list else set())
        for g in (x for x in games if x["store"] == s.id):
            k = g["skey"]
            if k in prev["seen"]:
                seen[k] = prev["seen"][k]
                continue
            known = ((prev["legacy"] and norm_title(g["title"]) in prev["titles"])
                     or norm_title(g["title"]) in old_titles)
            is_new = initialized and not known
            seen[k] = today if is_new else ""
            if is_new:
                added.append(f"{g['title']} ({s.name})" if multi_all else g["title"])
    others = [s for s in STORES if s not in ok_stores]  # en échec ou non sélectionnées : historique conservé
    carried_init = {s.id for s in others if s.id in prev["init"]}
    srcs = dict(prev["srcs"])
    srcs.update({s.id: s.src for s in ok_stores if getattr(s, "src", "")})
    for k, v in prev["seen"].items():
        if any(k.startswith(s.id + ":") for s in others):
            seen[k] = v

    # Pages à produire
    page_defs = []
    if single:
        page_defs.append((out.name, ok_stores))
    if per_platform:
        page_defs += [(f"{out.stem}_{s.id}{out.suffix}", [s]) for s in ok_stores]
    overrides = load_overrides()
    page_entries = [build_entries([g for g in games if g["store"] in {s.id for s in pst}], overrides)
                    for _, pst in page_defs]
    total_entries = sum(len(e) for e in page_entries)

    # Jeux sans page de boutique (Prime Gaming, Ubisoft, listes manuelles) : page Steam du jeu en dernier recours.
    def has_link(e):
        return any(g.get("link") for g in e["games"])
    need = {}
    for pe in page_entries:
        for e in pe:
            if not has_link(e):
                need.setdefault(norm_title(e["title"]), e["title"])
    todo = [(k, t) for k, t in need.items() if k not in CTX["lookup"]]
    if todo:
        found, flock = [0], threading.Lock()

        def look(kt):
            r = steam_lookup(kt[1])
            with flock:
                found[0] += 1
                progress("Steam : pages des jeux sans boutique", found[0], len(todo))
            return kt[0], r
        with ThreadPoolExecutor(max_workers=6) as ex:
            for k, r in ex.map(look, todo):
                if r is not None:
                    CTX["lookup"][k] = r

    # Jaquettes : réutilisées depuis les anciennes pages, sinon SteamGridDB, sinon la boutique.
    sgdb = SGDB if SGDB.logged_in() else None
    dead, broken, sem, lock = [False], [False], threading.Semaphore(4), threading.Lock()
    sg_errors, memo = [], {}
    counters = {"done": 0, "reused": 0, "rescaled": 0, "new": 0, "converted": 0}
    tool_ok = probe_image_tool()[2] is not None
    usable = prev["ok"] and not prev["legacy"]
    prev_w = prev["width"]

    def job(e):
        keys = [g["skey"] for g in e["games"]]
        hit = next((memo[k] for k in keys if k in memo), None)  # déjà préparée pour une autre page
        if hit:
            with lock:
                counters["done"] += 1
                counters["reused"] += 1
                progress("Jaquettes", counters["done"], total_entries)
            return hit
        old_any = next((prev["covers"][k] for k in keys if k in prev["covers"]), None) if usable else None
        cw = old_any[2] if old_any else 0  # largeur de l'image déjà présente (une image ne s'agrandit pas)
        old, rescaled = ((old_any[:2] if (old_any and not refresh and cw >= width) else None), False)
        foreign = bool(old) and tool_ok and needs_convert(old[0])  # ex. PNG d'origine, trop lourd
        if old and (cw > width or foreign):  # redimensionnement / conversion locale, sans retélécharger
            uri = rescale_uri(old[0], width, quality)
            old, rescaled = ((uri, old[1]), True) if uri else (None, False)
            if rescaled and foreign:
                with lock:
                    counters["converted"] += 1
        res, missed = None, False
        if old and old[1] == "sgdb":
            res = old
        else:
            known_miss = (not refresh) and all(k in prev["miss"] for k in keys)
            if sgdb and not dead[0] and not broken[0] and not known_miss:
                try:
                    with sem:
                        url = sgdb.find_thumb(e)
                    if url is None:
                        missed = True
                    else:
                        with sem:
                            data = http_get(url)
                        uri = process_image(data, width, quality) if data else ""
                        if uri:
                            res = (uri, "sgdb")
                except NotLoggedIn:
                    dead[0] = True
                except Exception as ex:  # signalé à la fin (et abandon si les échecs s'enchaînent)
                    with lock:
                        sg_errors.append(describe(ex, "SteamGridDB"))
                        if len(sg_errors) >= 8:
                            broken[0] = True
            elif sgdb and known_miss:
                missed = True
            if res is None:
                if old:
                    res = old
                else:
                    uri = store_cover(e, width, quality)
                    res = (uri, "store") if uri else (old_any[:2] if old_any else ("", ""))
        with lock:
            counters["done"] += 1
            counters["new" if not (old and res is old) else ("rescaled" if rescaled else "reused")] += 1
            progress("Jaquettes", counters["done"], total_entries)
            result = (res[0], res[1], missed)
            for k in keys:
                memo[k] = result
        return result

    names = {s.id: s.name for s in ok_stores}
    tags = {s.id: s.tag for s in ok_stores}
    files, per_store_count, total_both, total_covers = [], {}, 0, 0
    for (fname, pst), entries in zip(page_defs, page_entries):
        with ThreadPoolExecutor(max_workers=8) as ex:
            covers = list(ex.map(job, entries))
        total_covers += sum(1 for c in covers if c[0])
        ids = {s.id for s in pst}
        is_single = fname == out.name
        kept = ids | ({s.id for s in others} if is_single else set())  # historique repris dans la page unique
        multi = len(pst) > 1
        cards, n_new, miss = [], 0, set()
        for e, (uri, src, missed) in zip(entries, covers):
            keys = [g["skey"] for g in e["games"]]
            if missed and src != "sgdb":
                miss.update(keys)
            title = html.escape(e["title"])
            is_new = any(bool(seen.get(k)) and seen[k] >= limit for k in keys)
            n_new += is_new
            img = (f'<img src="{uri}" alt="{title}" loading="lazy">' if uri
                   else f'<div class="noimg">{title}</div>')
            inner = f"{img}<figcaption>{title}</figcaption>"
            links, done_stores = [], set()
            for g in e["games"]:  # un seul lien par boutique
                if g.get("link") and g["store"] not in done_stores:
                    done_stores.add(g["store"])
                    links.append({"n": names[g["store"]], "u": g["link"]})
            if len(links) == 1:
                inner = (f'<a class="lnk" href="{html.escape(links[0]["u"], quote=True)}" '
                         f'target="_blank" rel="noopener noreferrer" '
                         f'title="Ouvrir la page du jeu : {title}">{inner}</a>')
            elif links:
                data = html.escape(json.dumps(links, ensure_ascii=False), quote=True)
                inner = (f'<a class="lnk pick" href="{html.escape(links[0]["u"], quote=True)}" '
                         f'data-links="{data}" data-title="{title}" target="_blank" '
                         f'rel="noopener noreferrer" title="Choisir le site à ouvrir">{inner}</a>')
            else:  # aucune boutique ne propose de page pour ce jeu : page Steam (fenêtre de redirection)
                appid = CTX["lookup"].get(norm_title(e["title"]))
                steam_url = (f"https://store.steampowered.com/app/{appid}" if appid
                             else "https://store.steampowered.com/search/?term=" + quote(e["title"]))
                origin = html.escape(" + ".join(names[sid] for sid in e["stores"]))
                inner = (f'<a class="lnk steamfb" href="{html.escape(steam_url, quote=True)}" target="_blank" '
                         f'rel="noopener noreferrer" data-origin="{origin}" data-title="{title}" '
                         f'data-exact="{1 if appid else 0}" title="Voir ce jeu sur Steam">{inner}</a>')
            badge = '<span class="badge">Nouveau</span>' if is_new else ""
            tag = ('<span class="tags">' + "".join(
                f'<span class="tag {sid}">{tags[sid]}</span>' for sid in e["stores"]) + "</span>"
                   if multi else "")
            alt = " ".join(dict.fromkeys(html.escape(g["title"]).lower() for g in e["games"]))
            kjson = html.escape(json.dumps(keys, ensure_ascii=False), quote=True)
            cards.append(f'<figure class="card{" new" if is_new else ""}" data-s="{" ".join(e["stores"])}" '
                         f'data-k="{kjson}" data-c="{src}" data-t="{alt}">{badge}{tag}{inner}</figure>')

        both = sum(1 for e in entries if len(e["stores"]) > 1)
        total_both += both
        for s in pst:
            per_store_count[s.name] = sum(1 for e in entries if s.id in e["stores"])
        chips = ""
        if multi:
            counts = {s.id: sum(1 for e in entries if s.id in e["stores"]) for s in pst}
            chips = ('<div class="chips"><button class="chip on" data-s="">Tous</button>'
                     + "".join(f'<button class="chip" data-s="{s.id}">{s.name} ({counts[s.id]})</button>'
                               for s in pst)
                     + (f'<button class="chip" data-s="*">Sur plusieurs boutiques ({both})</button>'
                        if both else "") + "</div>")
        flt = (f'<label><input type="checkbox" id="onlynew"> Nouveautés ({n_new})</label>'
               if n_new else "")

        # Mémoire de l'application, conservée dans la page elle-même.
        epic = ({k: v for k, v in CTX["epic"].items() if k in CTX["epic_seen"]}
                if CTX["epic_seen"] else CTX["epic"]) if ("epic" in kept) else {}
        manual_titles = {norm_title(g["title"]) for g in games
                         if g["store"] in ids and any(s.id == g["store"] and s.has_list for s in pst)}
        state = {"v": FORMAT, "app": version_label(), "date": today, "width": width,
                 "seen": {k: v for k, v in seen.items() if sid_of(k) in kept},
                 "init": sorted(({s.id for s in ok_stores} | carried_init) & kept),
                 "srcs": {k: v for k, v in srcs.items() if k in kept},
                 "epic": epic,
                 "lookup": {k: v for k, v in CTX["lookup"].items()
                            if k in manual_titles or k in {norm_title(e["title"]) for e in entries if not has_link(e)}},
                 "miss": sorted(miss | {k for k in prev["miss"] if sid_of(k) in kept - ids}),
                 "manual": {s.id: MANUAL[s.id] for s in STORES
                            if s.has_list and MANUAL.get(s.id, "").strip() and s.id in kept}}
        state_json = json.dumps(state, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
        heading = f"Ma bibliothèque {pst[0].name}" if (not is_single and len(pst) == 1) else "Ma bibliothèque de jeux"
        page = (PAGE.replace("Ma bibliothèque de jeux", html.escape(heading))
                .replace("__N__", str(len(entries))).replace("__CHIPS__", chips)
                .replace("__FILTER__", flt).replace("__CARDS__", "\n".join(cards))
                .replace("__STATE__", state_json).replace("__VERSION__", version_label()))
        path = out.with_name(fname)
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(path.name + ".tmp")  # écriture atomique : l'ancienne page reste intacte en cas d'échec
        tmp.write_text(page, encoding="utf-8")
        os.replace(tmp, path)
        files.append({"name": path.name, "path": str(path), "label": ("page unique : " if (is_single and len(pst) > 1) else "") + " + ".join(s.name for s in pst),
                      "count": len(entries), "size_mb": round(len(page.encode()) / 1_048_576, 2)})

    if dead[0]:
        warnings.append("SteamGridDB : clé API refusée, reconnecte-toi (jaquettes des boutiques utilisées).")
    if sg_errors:
        warnings.append(f"SteamGridDB : {len(sg_errors)} requête(s) en échec ({sg_errors[0]})"
                        + (", abandon après 8 échecs" if broken[0] else "")
                        + " ; jaquettes des boutiques utilisées, SteamGridDB sera réessayé à la prochaine génération.")
    if CTX.get("noshrink"):
        warnings.append("Aucun outil de conversion d'images (Pillow, ImageMagick ou ffmpeg) : les images "
                        "lourdes ont été ignorées, les autres gardées telles quelles (PNG/JPEG d'origine, "
                        "fichier lourd). Installe Pillow pour obtenir des images WebP légères.")
    if not prev["ok"]:
        note = "aucun ancien fichier : toutes les images ont été préparées"
    elif prev["legacy"]:
        note = "ancien fichier d'une version précédente : images préparées de nouveau cette fois, elles seront réutilisées ensuite"
    elif refresh:
        note = "« Retraiter toutes les images » demandé"
    elif prev_w and prev_w != width:
        note = (f"taille changée ({prev_w} → {width} px) : " + (
            "images redimensionnées sans retéléchargement" if prev_w > width
            else "images retéléchargées, car une image ne peut pas être agrandie"))
    else:
        note = ""
    if counters["converted"]:
        note += (" ; " if note else "") + (f"{counters['converted']} image(s) d'un ancien format ou trop "
                                          "lourdes converties en WebP sans retéléchargement")

    return {"single": single, "per_platform": per_platform,
            "count": files[0]["count"] if single else sum(f["count"] for f in files), "covers": total_covers,
            "added": list(dict.fromkeys(added)), "both": total_both,
            "reused": counters["reused"] + counters["rescaled"], "rescaled": counters["rescaled"],
            "downloaded": counters["new"], "note": note,
            "per_store": [[n, c] for n, c in per_store_count.items()],
            "warnings": warnings, "files": files, "path": files[0]["path"],
            "size_mb": round(sum(f["size_mb"] for f in files), 2),
            "previous": {"found": prev["ok"], "legacy": prev["legacy"], "count": prev["count"]}}


# ------------------------------------------------------------------ interface web
UI = """<!DOCTYPE html>
<html lang="fr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Bibliothèque de jeux</title>
<style>
:root{--bg:#14141a;--fg:#eee;--card:#1f1f28;--muted:#9a9aa8;--accent:#e8a23a;--ok:#4cc38a;--err:#ff6b6b}
@media(prefers-color-scheme:light){:root{--bg:#f4f4f7;--fg:#1b1b22;--card:#fff;--muted:#666;--accent:#c77d00;--ok:#1a8a5a;--err:#c0392b}}
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,sans-serif;background:var(--bg);color:var(--fg);display:flex;justify-content:center;padding:32px 16px}
.wrap{width:100%;max-width:580px;min-width:0}
.panel{overflow-wrap:anywhere}
.col{min-width:0}
@media (min-width:900px){
.wrap{max-width:1120px}
.cols{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:0 20px;align-items:start}
}
@media (min-width:900px) and (min-height:720px){.col-right{position:sticky;top:20px}}
h1{font-size:1.5rem;margin:0 0 4px}.sub{color:var(--muted);margin:0 0 24px}
.panel{background:var(--card);border-radius:12px;padding:20px;margin-bottom:16px;box-shadow:0 2px 10px #0003}
.panel h2{font-size:1rem;margin:0 0 10px}
.panel h3{font-size:.78rem;text-transform:uppercase;letter-spacing:.05em;color:var(--muted);margin:16px 0 6px}
p{line-height:1.5;margin:8px 0}.muted{color:var(--muted);font-size:.9rem}
button,a.btn{display:inline-block;background:var(--accent);color:#111;border:0;border-radius:8px;padding:10px 18px;font-size:1rem;font-weight:600;cursor:pointer;text-decoration:none}
button.sec,a.sec{background:transparent;color:var(--fg);border:1px solid #8886}
button.small{padding:6px 12px;font-size:.85rem}
button:disabled{opacity:.5;cursor:default}
select{padding:8px;border-radius:8px;border:1px solid #8886;background:var(--bg);color:var(--fg);font-size:.9rem}
.modes label{display:flex;gap:6px;align-items:center;font-size:.95rem;cursor:pointer}
.modes{display:flex;flex-direction:column;gap:6px;margin:8px 0 12px}
.frow{padding:10px 0;border-top:1px solid #8883}.frow:first-child{border-top:0;padding-top:0}
.finfo{word-break:break-word}
input[type=text],input[type=password],textarea{width:100%;font-family:inherit;padding:10px 12px;border-radius:8px;border:1px solid #8886;background:var(--bg);color:var(--fg);font-size:.95rem;margin:8px 0}
.row{display:flex;gap:10px;flex-wrap:wrap;margin-top:12px}
.srow{display:flex;gap:12px;align-items:center;flex-wrap:wrap}.srow>button,.sbtns{margin-left:auto}
.sbtns{display:flex;gap:6px;flex-wrap:wrap;justify-content:flex-end}
details{margin:10px 0}summary{cursor:pointer;color:var(--accent);font-weight:600}
pre.snip{background:var(--bg);border:1px solid #8886;border-radius:8px;padding:10px;font-size:.78rem;white-space:pre-wrap;word-break:break-all;margin:8px 0;user-select:all}
.store{padding:10px 0;border-top:1px solid #8883}.store:first-child{border-top:0;padding-top:0}
.bar{height:10px;border-radius:99px;background:#8883;overflow:hidden;margin:12px 0 6px}
.bar>div{height:100%;width:0;background:var(--accent);transition:width .3s}
.ok{color:var(--ok)}.err{color:var(--err)}.warn{color:var(--accent)}.hidden{display:none}
ol{padding-left:20px;line-height:1.6;margin:8px 0}
ul.new{margin:6px 0;padding-left:20px;max-height:140px;overflow:auto;font-size:.9rem}
</style></head><body><div class="wrap">
<h1>Bibliothèque de jeux</h1><p class="sub">Une page web hors ligne avec toutes tes jaquettes (GOG, Epic, Steam…), à partager.</p>

<div class="cols"><div class="col col-left">
<div class="panel"><h2>Connexions</h2>
<h3>Boutiques avec connexion</h3><div id="stores"></div>
<h3>Visuels des jaquettes (facultatif)</h3><div id="services"></div>
<div class="row"><button class="sec small" id="recheck">Revérifier les connexions</button></div>
<p class="muted">Ton mot de passe n'est jamais vu par cette application : la connexion se fait sur le site de la boutique.</p></div>

<div class="panel" id="listsPanel"><h2>Boutiques sans connexion</h2>
<p class="muted">Ces boutiques n'offrent pas d'accès public à ton compte : renseigne simplement la liste de tes jeux.</p>
<div id="lists"></div></div>

</div>
<div class="col col-right">
<div class="panel"><h2>Ta bibliothèque</h2>
<p class="muted" id="last"></p>
<p class="muted hidden" id="hint">Connecte au moins une boutique pour commencer.</p>
<h3>Fichiers à générer</h3>
<div class="modes"><label><input type="checkbox" id="opt-single" checked> Un fichier unique avec toutes les plateformes</label>
<label><input type="checkbox" id="opt-per"> Un fichier par plateforme</label></div>
<p class="muted" id="prevline"></p>
<div class="row"><button class="sec small" id="prevbtn">Charger un ancien fichier…</button>
<input type="file" id="prevfile" accept=".html,text/html" class="hidden">
<select id="preset" title="Taille des images dans la page"><option value="legere">Images légères</option>
<option value="standard" selected>Images standard</option><option value="haute">Images haute qualité</option></select>
<label class="muted"><input type="checkbox" id="refresh"> Retraiter toutes les images</label></div>
<p class="muted" id="imgtool"></p>
<div class="row"><button id="gen">Générer / mettre à jour la page</button></div>
<div id="prog" class="hidden"><div class="bar"><div id="fill"></div></div><div class="muted" id="msg"></div></div>
<p class="err" id="generr"></p>
</div>

<div class="panel hidden" id="result">
<h2 class="ok">✓ Génération terminée</h2>
<p id="summary"></p><p class="warn" id="warn"></p><ul class="new hidden" id="newlist"></ul>
<div id="files"></div>
<div class="row"><button class="sec" id="folder">Ouvrir le dossier</button></div>
<p class="muted">Envoie simplement un fichier : il s'ouvre hors ligne dans n'importe quel navigateur.</p>
</div>

</div></div>

<p class="muted" style="text-align:center">Aucune base de données : l'historique et les images sont gardés dans la page générée. Seules tes connexions sont enregistrées (dossier ~/.config/gog-bibliotheque).</p>
<p class="muted" style="text-align:center">Version __VERSION__</p>
<div class="row" style="justify-content:center"><button class="sec" id="quit">Quitter l'application</button></div>
</div>
<script>
const T="__TOKEN__",$=id=>document.getElementById(id);
const api=(p,b)=>fetch(p,{method:b===undefined?'GET':'POST',headers:{'X-Token':T,'Content-Type':'application/json'},body:b===undefined?undefined:JSON.stringify(b)}).then(r=>r.json());
let presetTouched=false,timer=null,listOpen={},opened={},autoOpened={},stores=[],busy=false,anyLogged=false;
function el(tag,cls,text){const e=document.createElement(tag);if(cls)e.className=cls;if(text!==undefined)e.textContent=text;return e}
function updateGen(){$('gen').disabled=busy||!anyLogged}
function statusOf(s){const st=(s.status||{}).state,u=(s.status||{}).user;
 if(s.logged&&st==='checking')return['muted','● vérification…'];
 if(s.logged&&st==='offline')return['warn','● non vérifié (hors ligne ?)'];
 if(s.logged)return['ok','● connecté'+(u?' ('+u+')':'')];
 if(st==='expired')return['err','● session expirée, reconnecte-toi'];
 if(s.has_list&&s.count>0)return['ok','● liste : '+s.count+' jeu'+(s.count>1?'x':'')];
 return['muted','non connecté']}
function copyText(t,btn){const old=btn.textContent;
 (navigator.clipboard?navigator.clipboard.writeText(t):Promise.reject()).then(()=>{btn.textContent='Copié ✓'}).catch(()=>{btn.textContent='Copie impossible : sélectionne le texte'});
 setTimeout(()=>{btn.textContent=old},2500)}
function manualBox(wrap,s){
 wrap.appendChild(el('p','muted',s.help));
 const ta=el('textarea');ta.rows=8;ta.placeholder='Un jeu par ligne';wrap.appendChild(ta);
 api('/api/manual?store='+s.id).then(r=>{ta.value=r.text});
 const ok=el('button',null,'Enregistrer');
 ok.onclick=async()=>{await api('/api/manual',{store:s.id,text:ta.value});opened[s.id]=false;listOpen[s.id]=false;await refresh()};
 wrap.appendChild(ok)}
function loginBox(wrap,s){
 const ol=el('ol');s.steps.forEach(t=>ol.appendChild(el('li',null,t)));wrap.appendChild(ol);
 if(s.alt_steps&&s.alt_steps.length){const d=el('details'),sm=el('summary',null,s.alt_title||'Méthode alternative'),o2=el('ol');
  d.appendChild(sm);s.alt_steps.forEach(t=>o2.appendChild(el('li',null,t)));d.appendChild(o2);wrap.appendChild(d)}
 const a=el('a','btn sec',s.kind==='key'?'Obtenir ma clé API':'Ouvrir la connexion '+s.name);
 a.href=s.auth_url;a.target='_blank';a.rel='noopener';wrap.appendChild(a);
 (s.extra_links||[]).forEach(l=>{const b=el('a','btn sec',l.label);b.href=l.url;b.target='_blank';b.rel='noopener';wrap.appendChild(b)});
 if(s.snippet){wrap.appendChild(el('pre','snip',s.snippet));
  const cb=el('button','sec small','Copier le script');cb.onclick=()=>copyText(s.snippet,cb);wrap.appendChild(cb)}
 const err=el('p','err');
 if(s.kind==='key'){
  const inputs={};
  s.fields.forEach(f=>{const i=el('input');i.type=f.secret?'password':'text';i.placeholder=f.label;inputs[f.name]=i;wrap.appendChild(i)});
  const ok=el('button',null,'Valider');
  ok.onclick=async()=>{err.textContent='Connexion…';const v={};for(const k in inputs)v[k]=inputs[k].value;
   const r=await api('/api/login',{store:s.id,fields:v});
   if(r.ok){opened[s.id]=false;await refresh()}else err.textContent=r.error};
  wrap.appendChild(ok);wrap.appendChild(err);return}
 const inp=el('input');inp.type='text';inp.placeholder='… ou colle ici avec Ctrl+V';wrap.appendChild(inp);
 const ok=el('button',null,'Coller et valider');let sending=false;
 async function submit(v){if(sending||!v.trim())return;sending=true;inp.value='';err.textContent='Connexion…';
  const r=await api('/api/login',{store:s.id,url:v});sending=false;
  if(r.ok){opened[s.id]=false;await refresh()}else err.textContent=r.error}
 inp.addEventListener('paste',e=>{e.preventDefault();submit((e.clipboardData||window.clipboardData).getData('text'))});
 inp.addEventListener('keydown',e=>{if(e.key==='Enter')submit(inp.value)});
 ok.onclick=async()=>{err.textContent='';
  try{submit(await navigator.clipboard.readText())}
  catch(e){err.textContent='Presse-papiers inaccessible : clique dans le champ et fais Ctrl+V.'}};
 wrap.appendChild(ok);wrap.appendChild(err)}
function renderStores(){
 ['stores','services','lists'].forEach(id=>$(id).innerHTML='');
 stores.forEach(s=>{
  const pure=s.kind==='manual';
  const box=pure?$('lists'):(s.service?$('services'):$('stores'));
  const wrap=el('div','store'),row=el('div','srow'),bx=el('div','sbtns');
  row.appendChild(el('strong',null,s.name));
  if(pure){
   row.appendChild(el('span',s.count?'ok':'muted',s.count?('● '+s.count+' jeu'+(s.count>1?'x':'')):'liste vide'));
   const b=el('button','sec small',opened[s.id]?'Fermer':'Modifier la liste');
   b.onclick=async()=>{opened[s.id]=!opened[s.id];await refresh()};bx.appendChild(b);
  }else{
   const [scls,stxt]=statusOf(s);row.appendChild(el('span',scls,stxt));
   if(s.has_list){const lb=el('button','sec small',listOpen[s.id]?'Fermer la liste':'Liste manuelle');
    lb.onclick=async()=>{listOpen[s.id]=!listOpen[s.id];await refresh()};bx.appendChild(lb)}
   const b=el('button','sec small',s.logged?'Se déconnecter':(opened[s.id]?'Annuler':'Se connecter'));
   b.onclick=async()=>{if(s.logged){await api('/api/logout',{store:s.id})}else{opened[s.id]=!opened[s.id]}await refresh()};bx.appendChild(b);
  }
  row.appendChild(bx);wrap.appendChild(row);
  if(!pure&&['offline','expired'].includes((s.status||{}).state)&&s.status.detail)wrap.appendChild(el('p','muted',s.status.detail));
  if(pure){if(opened[s.id])manualBox(wrap,s)}
  else{if(!s.logged&&opened[s.id])loginBox(wrap,s);if(s.has_list&&listOpen[s.id])manualBox(wrap,s)}
  box.appendChild(wrap)});
 $('listsPanel').classList.toggle('hidden',!stores.some(x=>x.kind==='manual'))}
function showTool(i){const e=$('imgtool');
 if(i&&i.tool){e.textContent='Conversion des images : '+i.tool+' → '+i.format+'.';e.className='muted'}
 else{e.textContent="⚠ Aucun outil de conversion d'images trouvé (Pillow, ImageMagick ou ffmpeg) : les images ne seront ni réduites ni converties en WebP. Installe Pillow, par exemple : nix-shell -p 'python3.withPackages (p: [ p.pillow ])'";e.className='warn'}}
function showPrev(p){p=p||{source:'none'};let t;
 if(p.source==='none')t="Aucun ancien fichier : tous tes jeux seront considérés comme déjà connus (pas de badge « Nouveau »).";
 else{t=(p.source==='manual'?'Ancien fichier chargé : ':'Ancien fichier détecté : ')+p.name+' ('+p.count+' jeux'+(p.date?', généré le '+p.date:'')+'). Il sert à repérer les nouveaux jeux et à réutiliser les images.';
  if(p.legacy)t+=" Ancien format : les nouveaux jeux sont repérés par leur titre."}
 $('prevline').textContent=t;if(p.preset&&!presetTouched)$('preset').value=p.preset}
async function refresh(){const s=await api('/api/state');stores=s.stores;
 stores.forEach(x=>{if((x.status||{}).state==='expired'&&!autoOpened[x.id]){autoOpened[x.id]=true;opened[x.id]=true}});
 renderStores();
 if(stores.some(x=>x.logged&&(x.status||{}).state==='checking'))setTimeout(refresh,900);
 anyLogged=stores.some(x=>(x.usable===undefined?x.logged:x.usable)&&!x.service);updateGen();$('hint').classList.toggle('hidden',anyLogged);
 $('last').textContent=s.last?('Dernière génération : '+s.last):'Aucune page générée pour le moment.';showPrev(s.previous);showTool(s.images)}
function render(st){
 busy=st.state==='running';updateGen();
 $('prog').classList.toggle('hidden',!busy);
 if(busy){$('fill').style.width=(st.total?100*st.done/st.total:5)+'%';
  $('msg').textContent=st.step+(st.total?' ('+st.done+'/'+st.total+')':' ('+st.done+')')}
 if(st.state==='error'){$('generr').textContent=st.error;clearInterval(timer);timer=null;refresh()}
 if(st.state==='done'){clearInterval(timer);timer=null;$('generr').textContent='';
  const r=st.result;$('result').classList.remove('hidden');
  const parts=r.per_store.map(p=>p[0]+' : '+p[1]).join(', ');
  $('summary').textContent=(r.single?r.count+' jeux uniques (':r.count+' jeux répartis en '+r.files.length+' pages (')+parts+(r.both?', dont '+r.both+' sur plusieurs boutiques':'')+'), '+r.size_mb+' Mo'+(r.single&&r.per_platform?' (page unique + '+(r.files.length-1)+' pages par plateforme)':'')+'. Images : '+r.reused+' réutilisées'+(r.rescaled?' (dont '+r.rescaled+' redimensionnées)':'')+', '+r.downloaded+' traitées.'+(r.note?' Note : '+r.note+'.':'');
  $('warn').textContent=r.warnings.join(' ');
  const fl=$('files');fl.innerHTML='';
  r.files.forEach(f=>{const row=el('div','frow'),info=el('div','finfo');
   info.appendChild(el('strong',null,f.name));info.appendChild(el('span','muted',' — '+f.label+' · '+f.count+' jeu'+(f.count>1?'x':'')+' · '+f.size_mb+' Mo'));
   row.appendChild(info);const bx=el('div','row'),dl=el('button',null,'Télécharger'),op=el('button','sec','Ouvrir');
   dl.onclick=()=>{location.href='/download?t='+T+'&f='+encodeURIComponent(f.name)};
   op.onclick=()=>api('/api/open',{what:'file',name:f.name});
   bx.appendChild(dl);bx.appendChild(op);row.appendChild(bx);fl.appendChild(row)});
  const l=$('newlist');l.innerHTML='';
  if(r.added.length){l.classList.remove('hidden');
   $('summary').textContent+=' '+r.added.length+' nouveau(x) jeu(x) :';
   r.added.forEach(t=>l.appendChild(el('li',null,t)))}else l.classList.add('hidden');
  refresh()}}
async function poll(){render(await api('/api/status'))}
$('gen').onclick=async()=>{$('generr').textContent='';
 const single=$('opt-single').checked,per=$('opt-per').checked;
 if(!single&&!per){$('generr').textContent='Coche au moins un type de fichier.';return}
 $('result').classList.add('hidden');
 await api('/api/generate',{preset:$('preset').value,refresh:$('refresh').checked,single:single,per_platform:per});if(!timer)timer=setInterval(poll,600);poll()};
$('preset').onchange=()=>{presetTouched=true};
$('prevbtn').onclick=()=>$('prevfile').click();
$('prevfile').onchange=()=>{const f=$('prevfile').files[0];if(!f)return;const rd=new FileReader();
 rd.onload=async()=>{const r=await api('/api/previous',{name:f.name,text:rd.result});
  if(!r.ok)$('prevline').textContent='⚠ '+r.error;else await refresh();$('prevfile').value=''};
 rd.readAsText(f)};
$('recheck').onclick=async()=>{await api('/api/check',{});await refresh()};
$('folder').onclick=()=>api('/api/open',{what:'folder'});
$('quit').onclick=async()=>{await api('/api/quit',{});document.body.innerHTML='<p style="padding:40px;font-family:sans-serif">Application arrêtée. Tu peux fermer cet onglet.</p>'};
refresh();api('/api/status').then(st=>{if(st.state==='running'){timer=setInterval(poll,600)}});
</script></body></html>"""


class App:
    def __init__(self):
        self.token = secrets.token_urlsafe(24)
        self.status = {"state": "idle", "step": "", "done": 0, "total": 0}
        self.lock = threading.Lock()
        self.server = None
        self.checks = {}
        self.previous_text = None      # page choisie à la main (sinon : la dernière page générée)
        self.previous_summary = None
        self._auto = None              # (signature des fichiers, résultat de l'analyse)
        self.files = {}                # pages produites par la dernière génération (nom -> chemin)

    def status_of(self, store):
        c = self.checks.get(store.id, {"state": "unknown"})
        if not store.connected() and c["state"] != "expired":
            return {"state": "none"}
        return c

    def start_check(self):
        """Vérifie en arrière-plan la connexion de chaque boutique et service."""
        for s in STORES + SERVICES:
            if s.connected():
                self.checks[s.id] = {"state": "checking"}
                threading.Thread(target=lambda st=s: self.checks.__setitem__(st.id, st.check()),
                                 daemon=True).start()

    @staticmethod
    def _summary(p, source, name):
        return {"source": source, "name": name, "count": p["count"], "date": p["date"],
                "legacy": p["legacy"], "preset": preset_of(p["width"]) if p["width"] else ""}

    def previous_info(self):
        """Résumé de l'ancienne page qui sert à repérer les nouveaux jeux."""
        if self.previous_text is not None:
            return self.previous_summary
        sig = previous_signature(OUTPUT)
        if not sig:
            return {"source": "none"}
        if not self._auto or self._auto[0] != sig:
            self._auto = (sig, load_previous_set(OUTPUT))
        p = self._auto[1]
        if not p["ok"]:
            return {"source": "none"}
        return self._summary(p, "auto", ", ".join(p.get("files") or [OUTPUT.name]))

    def load_previous(self, name, text):
        p = parse_previous(text)
        if not p["ok"]:
            raise ValueError("Ce fichier n'est pas une page générée par cette application.")
        self.previous_text = text
        self.previous_summary = self._summary(p, "manual", name)
        for sid, txt in p["manual"].items():
            MANUAL[sid] = txt

    def progress(self, step, done, total):
        with self.lock:
            self.status.update(step=step, done=done, total=total)

    def run_generate(self, preset, refresh, single, per_platform):
        try:
            res = generate(self.progress, previous=self.previous_text, preset=preset, refresh=refresh,
                           single=single, per_platform=per_platform)
            st = {"state": "done", "result": res}
            self.files = {f["name"]: Path(f["path"]) for f in res["files"]}
            self.previous_text, self.previous_summary, self._auto = None, None, None
        except NotLoggedIn:
            st = {"state": "error", "error": "Aucune boutique connectée."}
        except Exception as e:
            st = {"state": "error", "error": f"Erreur : {e}"}
        with self.lock:
            self.status = st

    def start_generate(self, opts=None):
        opts = opts or {}
        preset = opts.get("preset") if opts.get("preset") in PRESETS else "standard"
        single, per_platform = bool(opts.get("single", True)), bool(opts.get("per_platform", False))
        with self.lock:
            if self.status.get("state") == "running":
                return
            self.status = {"state": "running", "step": "Démarrage", "done": 0, "total": 0}
        threading.Thread(target=self.run_generate,
                         args=(preset, bool(opts.get("refresh")), single, per_platform), daemon=True).start()


def last_generated():
    times = [p.stat().st_mtime for p in previous_candidates(OUTPUT)]
    return time.strftime("%d/%m/%Y %H:%M", time.localtime(max(times))) if times else ""


def xdg_open(path):
    try:
        subprocess.Popen(["xdg-open", str(path)], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL)
    except Exception:
        pass


def make_handler(app):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def send_json(self, obj, code=200):
            body = json.dumps(obj).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def authorized(self):
            tok = self.headers.get("X-Token") or parse_qs(urlparse(self.path).query).get("t", [""])[0]
            return secrets.compare_digest(tok, app.token)

        def do_GET(self):
            path = urlparse(self.path).path
            if path == "/":
                body = UI.replace("__TOKEN__", app.token).replace("__VERSION__", version_label()).encode()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif not self.authorized():
                self.send_json({"error": "non autorisé"}, 403)
            elif path == "/api/state":
                self.send_json({"stores": [dict(s.info(), status=app.status_of(s)) for s in STORES + SERVICES],
                                "last": last_generated(), "exists": OUTPUT.exists(),
                                "previous": app.previous_info(), "images": image_tool_info()})
            elif path == "/api/status":
                with app.lock:
                    self.send_json(dict(app.status))
            elif path == "/api/manual":
                try:
                    store = get_store(parse_qs(urlparse(self.path).query).get("store", [""])[0])
                    self.send_json({"text": store.read_text() if store.has_list else ""})
                except StopIteration:
                    self.send_json({"text": ""})
            elif path == "/download":
                name = parse_qs(urlparse(self.path).query).get("f", [""])[0]
                target = app.files.get(name) or OUTPUT
                if not target.exists():
                    return self.send_json({"error": "aucun fichier"}, 404)
                data = target.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Disposition",
                                 f"attachment; filename*=UTF-8''{quote(target.name)}")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
            else:
                self.send_json({"error": "introuvable"}, 404)

        def do_POST(self):
            if not self.authorized():
                return self.send_json({"error": "non autorisé"}, 403)
            n = int(self.headers.get("Content-Length") or 0)
            try:
                body = json.loads(self.rfile.read(n) or b"{}")
            except ValueError:
                body = {}
            path = urlparse(self.path).path
            if path == "/api/login":
                try:
                    store = get_store(body.get("store"))
                    if store.fields:
                        store.login_fields(body.get("fields") or {})
                    else:
                        store.login(body.get("url", ""))
                    app.checks[store.id] = store.check()
                    self.send_json({"ok": True})
                except Exception as e:
                    self.send_json({"ok": False, "error": str(e)})
            elif path == "/api/generate":
                app.start_generate(body)
                self.send_json({"ok": True})
            elif path == "/api/previous":
                try:
                    app.load_previous(str(body.get("name", "")), str(body.get("text", "")))
                    self.send_json({"ok": True, "info": app.previous_info()})
                except ValueError as e:
                    self.send_json({"ok": False, "error": str(e)})
            elif path == "/api/logout":
                try:
                    store = get_store(body.get("store"))
                    store.logout()
                    app.checks[store.id] = {"state": "none"}
                except StopIteration:
                    pass
                self.send_json({"ok": True})
            elif path == "/api/check":
                app.start_check()
                self.send_json({"ok": True})
            elif path == "/api/manual":
                try:
                    store = get_store(body.get("store"))
                    if not store.has_list:
                        raise StopIteration
                    store.write_text(str(body.get("text", ""))[:200000])
                    self.send_json({"ok": True, "count": store.count()})
                except StopIteration:
                    self.send_json({"ok": False}, 400)
            elif path == "/api/open":
                target = app.files.get(str(body.get("name", ""))) or OUTPUT
                if body.get("what") == "folder":
                    xdg_open(target.parent)
                elif target.exists():
                    xdg_open(target)
                self.send_json({"ok": True})
            elif path == "/api/quit":
                self.send_json({"ok": True})
                threading.Thread(target=app.server.shutdown, daemon=True).start()
            else:
                self.send_json({"error": "introuvable"}, 404)

    return H


def run_ui():
    app = App()
    app.server = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(app))
    url = f"http://127.0.0.1:{app.server.server_address[1]}/"
    seed_manual(load_previous_set(OUTPUT))
    app.start_check()
    print(f"Interface : {url}\n(Ctrl+C ou bouton « Quitter » pour arrêter)")
    threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try:
        app.server.serve_forever()
    except KeyboardInterrupt:
        pass
    app.server.server_close()


# -------------------------------------------------------------- mode ligne de cmd
def run_auto(previous_path=None, preset="standard", refresh=False, single=True, per_platform=False):
    last = [""]

    def progress(step, done, total):
        line = f"{step} {done}/{total}" if total else f"{step} ({done})"
        if line != last[0] and (done == total or done % 25 == 0):
            print(line)
            last[0] = line

    previous = None
    if previous_path:
        try:
            previous = Path(previous_path).expanduser().read_text("utf-8", errors="ignore")
        except OSError as e:
            sys.exit(f"Ancien fichier illisible : {e}")
        if not parse_previous(previous)["ok"]:
            sys.exit("Ce fichier n'est pas une page générée par cette application.")
    seed_manual(parse_previous(previous) if previous is not None else load_previous_set(OUTPUT))
    labels = {"ok": "connecté", "expired": "session expirée (reconnecte-toi via l'interface)",
              "offline": "non vérifié (hors ligne ?)", "none": "non connecté"}
    for s in STORES + SERVICES:
        c = s.check()
        print(f"{s.name} : {labels[c['state']]}" + (f" ({c['user']})" if c.get("user") else ""))
    try:
        res = generate(progress, previous=previous, preset=preset, refresh=refresh,
                       single=single, per_platform=per_platform)
    except NotLoggedIn:
        sys.exit("Aucune boutique connectée : lance d'abord l'interface (sans --auto).")
    except Exception as e:
        sys.exit(f"Erreur : {e}")
    for f in res["files"]:
        print(f"Terminé : {f['path']} ({f['label']} : {f['count']} jeux, {f['size_mb']} Mo)")
    p = res["previous"]
    print("Ancienne page : " + (f"{p['count']} jeux" + (" (ancien format)" if p["legacy"] else "")
                                if p["found"] else "aucune (pas de badge « Nouveau » cette fois)"))
    print(f"Images : {res['reused']} réutilisées" + (f" (dont {res['rescaled']} redimensionnées)" if res["rescaled"] else "")
          + f", {res['downloaded']} traitées" + (f" - {res['note']}" if res["note"] else ""))
    for w in res["warnings"]:
        print("  ! ", w)
    for t in res["added"]:
        print("  + nouveau :", t)


def clean_legacy():
    """Supprime les fichiers de l'ancienne version (base de données locale)."""
    names = ["cache", "state.json", "epic_catalog.json", "cover_lookup.json"] + [
        f"jeux_{s.id}.txt" for s in STORES if s.has_list]
    found = [CONFIG / n for n in names if (CONFIG / n).exists()]
    if not found:
        print("Rien à nettoyer.")
        return
    print("Fichiers de l'ancienne version :")
    for p in found:
        print("  ", p)
    if any(p.name.startswith("jeux_") for p in found):
        print("Attention : les listes jeux_*.txt sont désormais conservées dans la page HTML. "
              "Génère ta page avant de les supprimer.")
    if input("Les supprimer ? [o/N] ").strip().lower() != "o":
        print("Rien n'a été supprimé.")
        return
    for p in found:
        shutil.rmtree(p) if p.is_dir() else p.unlink()
    try:
        CONFIG.rmdir()  # seulement s'il est vide (les connexions y restent sinon)
    except OSError:
        pass
    print("Nettoyage terminé. Tes connexions (jetons) ont été conservées.")


def run_diagnostic():
    """Teste l'accès réseau et les certificats SSL vers chaque service."""
    print(f"gog_library {version_label()}")
    if ssl is None:
        print(f"Python {sys.version.split()[0]} | SANS support SSL (module _ssl absent)")
        print("Transport HTTPS    :", f"curl ({CURL}), en secours" if CURL else "AUCUN")
    else:
        print(f"Python {sys.version.split()[0]} | {ssl.OPENSSL_VERSION}")
        print("Transport HTTPS    : Python (ssl)")
        print("Chemins SSL par défaut :", ssl.get_default_verify_paths().cafile or "(aucun)")
    print("SSL_CERT_FILE      =", os.environ.get("SSL_CERT_FILE", "(non défini)"))
    print("NIX_SSL_CERT_FILE  =", os.environ.get("NIX_SSL_CERT_FILE", "(non défini)"))
    print("Bundle chargé      =", "(sans objet : curl utilise ses propres certificats)" if ssl is None
          else CA_BUNDLE or "(aucun trouvé, certificats par défaut de Python)")
    t = image_tool_info()
    img_tool = (f"{t['tool']} -> {t['format']}" if t["tool"]
                else "AUCUN (Pillow, ImageMagick ou ffmpeg requis : sans eux, images PNG/JPEG d'origine)")
    print("Réduction d'images :", img_tool)
    print("Connexions enregistrées :", end=" ")
    saved = [x for x in STORES + SERVICES if x.connected()]
    print("" if saved else "(aucune)")
    for x in saved:
        c = x.check()  # n'envoie aucun mot de passe ; supprime les jetons d'une session expirée
        print(f"   {x.name} : {c['state']}" + (f" ({c['user']})" if c.get("user") else "")
              + (f" — {c['detail']}" if c.get("detail") else ""))
    print()
    targets = [("GOG (connexion)", "https://auth.gog.com/"),
               ("GOG (bibliothèque)", "https://embed.gog.com/"),
               ("Epic (connexion)", "https://account-public-service-prod03.ol.epicgames.com/"),
               ("Epic (bibliothèque)", "https://library-service.live.use1a.on.epicgames.com/"),
               ("Epic (catalogue)", "https://catalog-public-service-prod06.ol.epicgames.com/"),
               ("Steam (API)", "https://api.steampowered.com/"),
               ("Steam (images)", "https://cdn.cloudflare.steamstatic.com/"),
               ("SteamGridDB", "https://www.steamgriddb.com/api/v2/"),
               ("Ubisoft (connexion)", "https://connect.ubisoft.com/"),
               ("Ubisoft (API)", "https://public-ubiservices.ubi.com/"),
               ("Amazon (connexion)", "https://api.amazon.com/"),
               ("Amazon (bibliothèque)", "https://gaming.amazon.com/"),
               ("itch.io", "https://api.itch.io/")]
    for name, url in targets:
        try:
            http_get(url, timeout=15)
            print(f"  OK      {name}")
        except urllib.error.HTTPError as e:   # le serveur a répondu : réseau et SSL fonctionnent
            print(f"  OK      {name} (réponse HTTP {e.code}, normal sans identifiants)")
        except Exception as e:
            print(f"  ÉCHEC   {name} : {describe(e, name)}")


def install_shortcut():
    apps = Path.home() / ".local/share/applications"
    apps.mkdir(parents=True, exist_ok=True)
    f = apps / "gog-bibliotheque.desktop"
    f.write_text(
        "[Desktop Entry]\nType=Application\nName=Bibliothèque de jeux\n"
        "Comment=Générer une page web de ma bibliothèque GOG / Epic Games\n"
        f'Exec=python3 "{Path(__file__).resolve()}"\nTerminal=false\n'
        "Icon=applications-games\nCategories=Game;Utility;\n", encoding="utf-8")
    print(f"Lanceur créé : {f}\nCherche « Bibliothèque de jeux » dans ton menu d'applications.")


def main():
    global OUTPUT
    ap = argparse.ArgumentParser(description="Page HTML hors ligne de ta bibliothèque de jeux")
    ap.add_argument("--version", action="version", version=f"gog_library {version_label()}")
    ap.add_argument("--auto", action="store_true", help="génère sans interface")
    ap.add_argument("--install-shortcut", action="store_true", help="crée un lanceur")
    ap.add_argument("--diagnostic", action="store_true", help="teste le réseau et les certificats SSL")
    ap.add_argument("--nettoyer", action="store_true",
                    help="supprime les fichiers de l'ancienne version (cache, historique)")
    ap.add_argument("--out", help="fichier HTML de sortie")
    ap.add_argument("--previous", help="ancienne page à utiliser (nouveaux jeux, images déjà prêtes)")
    ap.add_argument("--taille", choices=list(PRESETS), default="standard", help="taille des images")
    ap.add_argument("--refresh-images", action="store_true", help="retraite toutes les images")
    ap.add_argument("--par-plateforme", action="store_true",
                    help="génère aussi une page par plateforme")
    ap.add_argument("--sans-page-unique", action="store_true",
                    help="ne génère pas la page unique (à combiner avec --par-plateforme)")
    a = ap.parse_args()
    if ssl is None and not (a.install_shortcut or a.nettoyer):
        if not CURL:
            print(NO_TLS_HELP, file=sys.stderr)
            if not a.diagnostic:
                sys.exit(1)
        elif not a.diagnostic:
            print("Note : ce Python n'a pas de support SSL, curl est utilisé à la place.")
    if a.out:
        OUTPUT = Path(a.out).expanduser().resolve()
    if a.diagnostic:
        run_diagnostic()
    elif a.nettoyer:
        clean_legacy()
    elif a.install_shortcut:
        install_shortcut()
    elif a.auto:
        if a.sans_page_unique and not a.par_plateforme:
            sys.exit("--sans-page-unique nécessite --par-plateforme (sinon aucun fichier ne serait généré).")
        run_auto(a.previous, a.taille, a.refresh_images, not a.sans_page_unique, a.par_plateforme)
    else:
        run_ui()


if __name__ == "__main__":
    main()
