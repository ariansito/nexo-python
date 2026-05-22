#!/usr/bin/env python3
"""
NEXO — 2D office metaverse backend
Python/FastAPI port — API-compatible with the original Node.js server.
"""
from __future__ import annotations

import asyncio
import base64
import datetime
import hashlib
import json
import math
import mimetypes
import os
import re
import secrets
import time
from pathlib import Path
from typing import Any, Optional

from fastapi import FastAPI, Request, Response, WebSocket, WebSocketDisconnect
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import (
    FileResponse,
    JSONResponse,
    PlainTextResponse,
    StreamingResponse,
)
from fastapi.staticfiles import StaticFiles

# ── Configuration ──────────────────────────────────────────────────────────────
PORT       = int(os.environ.get("PORT", 3000))
ADMIN_USER = os.environ.get("ADMIN_USERNAME", "arian").lower()
BASE_DIR   = Path(__file__).parent
DATA_DIR   = Path(os.environ.get("DATA_DIR",   str(BASE_DIR / "data")))
PUBLIC     = Path(os.environ.get("PUBLIC_DIR", str(BASE_DIR / "public")))

UPLOADS_DIR  = DATA_DIR / "uploads"
SOUNDS_DIR   = UPLOADS_DIR / "sounds"
WORLDS_DIR   = DATA_DIR / "worlds"

for _d in [DATA_DIR, UPLOADS_DIR, SOUNDS_DIR, WORLDS_DIR]:
    _d.mkdir(parents=True, exist_ok=True)

USERS_FILE           = DATA_DIR / "users.json"
WORLDS_INDEX         = WORLDS_DIR / "_index.json"
UPLOADS_META         = UPLOADS_DIR / "_index.json"
WIDGET_DEFAULTS_FILE = DATA_DIR / "widget_defaults.json"
SOUNDBOARD_FILE      = DATA_DIR / "soundboard.json"
MONITOR_RECORDS_FILE = DATA_DIR / "monitor_records.json"
TICKETS_FILE         = DATA_DIR / "tickets.json"
MAP_FILE             = PUBLIC / "map.json"
PANEL_FILE           = BASE_DIR.parent / "monitor-panel.html"

COLORS = ["#6366f1","#22c55e","#f59e0b","#ef4444","#06b6d4","#ec4899","#84cc16","#f97316"]

# ── JSON helpers ───────────────────────────────────────────────────────────────
def _load(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text("utf-8"))
    except Exception:
        return default

def _save(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False), "utf-8")

def load_users():           return _load(USERS_FILE, [])
def save_users(u):          _save(USERS_FILE, u)
def load_worlds_index():    return _load(WORLDS_INDEX, [])
def save_worlds_index(idx): _save(WORLDS_INDEX, idx)
def world_file(wid: str):   return WORLDS_DIR / f"{wid}.json"
def load_uploads_meta():    return _load(UPLOADS_META, [])
def save_uploads_meta(m):   _save(UPLOADS_META, m)
def load_widget_defaults(): return _load(WIDGET_DEFAULTS_FILE, None)
def save_widget_defaults(d):_save(WIDGET_DEFAULTS_FILE, d)
def load_soundboard():      return _load(SOUNDBOARD_FILE, [None]*5)
def save_soundboard(b):     _save(SOUNDBOARD_FILE, b)
def load_monitor_records(): return _load(MONITOR_RECORDS_FILE, [])
def save_monitor_records(r):_save(MONITOR_RECORDS_FILE, r)
def load_tickets():         return _load(TICKETS_FILE, [])
def save_tickets(t):        _save(TICKETS_FILE, t)

def _iso_now() -> str:
    return datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%S.000Z")

def _ts_to_float(s: str) -> float:
    try:
        return datetime.datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
    except Exception:
        return 0.0

# ── World migration ────────────────────────────────────────────────────────────
def _migrate_default_world() -> None:
    if load_worlds_index():
        return
    legacy = PUBLIC / "map.json"
    map_data: dict = {"worldW": 2000, "worldH": 1500, "rooms": [], "walls": [], "floors": [], "items": []}
    try:
        map_data = json.loads(legacy.read_text("utf-8"))
    except Exception:
        pass
    wid = f"world_{int(time.time() * 1000)}"
    _save(world_file(wid), {"name": "Oficina Principal", **map_data})
    save_worlds_index([{"id": wid, "name": "Oficina Principal", "created": _iso_now()}])
    print(f"[worlds] Migrado map.json → mundo 'Oficina Principal' ({wid})")

_migrate_default_world()

# ── Auth ───────────────────────────────────────────────────────────────────────
_SCRYPT_N, _SCRYPT_R, _SCRYPT_P = 16384, 8, 1

def hash_password(password: str) -> str:
    salt = secrets.token_hex(16)
    dk = hashlib.scrypt(password.encode(), salt=salt.encode(),
                        n=_SCRYPT_N, r=_SCRYPT_R, p=_SCRYPT_P, dklen=64)
    return f"scrypt:{salt}:{dk.hex()}"

def verify_password(password: str, stored: str) -> bool:
    if stored.startswith("scrypt:"):
        _, salt, stored_hash = stored.split(":")
        dk = hashlib.scrypt(password.encode(), salt=salt.encode(),
                            n=_SCRYPT_N, r=_SCRYPT_R, p=_SCRYPT_P, dklen=64)
        return secrets.compare_digest(dk.hex(), stored_hash)
    # Legacy SHA-256 (migration path)
    legacy = hashlib.sha256(password.encode()).hexdigest()
    return legacy == stored

# ── Sessions ───────────────────────────────────────────────────────────────────
SESSION_TTL = 8 * 3600
_sessions: dict[str, dict] = {}

def create_session(username: str) -> str:
    token = secrets.token_hex(32)
    _sessions[token] = {"username": username, "expires_at": time.time() + SESSION_TTL}
    return token

def get_session(token: Optional[str]) -> Optional[dict]:
    if not token:
        return None
    sess = _sessions.get(token)
    if not sess:
        return None
    if time.time() > sess["expires_at"]:
        _sessions.pop(token, None)
        return None
    return sess

# ── Rate limiting ──────────────────────────────────────────────────────────────
_MAX_ATTEMPTS = 5
_BLOCK_SECS   = 15 * 60
_login_attempts: dict[str, dict] = {}

def check_rate_limit(ip: str) -> bool:
    entry = _login_attempts.get(ip)
    if not entry:
        return True
    blocked_until = entry.get("blocked_until", 0)
    if blocked_until and time.time() < blocked_until:
        return False
    return True

def record_failed_attempt(ip: str) -> None:
    entry = _login_attempts.get(ip, {"count": 0})
    entry["count"] += 1
    if entry["count"] >= _MAX_ATTEMPTS:
        entry["blocked_until"] = time.time() + _BLOCK_SECS
    _login_attempts[ip] = entry

def clear_attempts(ip: str) -> None:
    _login_attempts.pop(ip, None)

# ── Rooms ──────────────────────────────────────────────────────────────────────
_rooms: list[dict] = []
_room_music: dict[str, dict] = {}

def get_room_id(x: float, y: float) -> Optional[str]:
    for r in _rooms:
        if r["x"] <= x <= r["x"] + r["w"] and r["y"] <= y <= r["y"] + r["h"]:
            return r["id"]
    return None

def reload_rooms_from_data(data: Any) -> None:
    global _rooms
    rooms_data = [] if isinstance(data, list) else (data.get("rooms") or [])
    _rooms = [
        {"id": r["id"], "name": r.get("name", r["id"]),
         "x": float(r["x"]), "y": float(r["y"]),
         "w": float(r["w"]), "h": float(r["h"])}
        for r in rooms_data
    ]

def reload_rooms() -> None:
    try:
        data = json.loads(MAP_FILE.read_text("utf-8"))
        reload_rooms_from_data(data)
    except Exception:
        global _rooms
        _rooms = []

reload_rooms()

# ── Players / combat ───────────────────────────────────────────────────────────
MAX_HP         = 10
RESPAWN_DELAY  = 1.5
ATTACK_COOLDOWN= 0.8
HIT_RANGE      = 60
HIT_CONE       = math.pi * 0.39
FACING_ANGLES  = [math.pi/2, math.pi, -math.pi/2, 0]
KNOCKBACK_DIST = 32
COMBAT_SPAWN_X = 1510
COMBAT_SPAWN_Y = 1380

_players:   dict[str, dict] = {}
_next_id    = [1]
_color_idx  = [0]

def validate_avatar(av: Any) -> dict:
    if not av or not isinstance(av, dict):
        return {"character": 0, "facing": 0}
    return {
        "character": max(0, min(3, int(av.get("character") or 0))),
        "facing":    max(0, min(3, int(av.get("facing")    or 0))),
        "inKart":    bool(av.get("inKart", False)),
    }

def save_player_position(username: str, x: float, y: float) -> None:
    try:
        users = load_users()
        for u in users:
            if u["username"] == username:
                u["position"] = {"x": round(x), "y": round(y)}
                save_users(users)
                break
    except Exception:
        pass

def purge_old_tickets(tickets: list) -> list:
    if len(tickets) <= 5000:
        return tickets
    cutoff = time.time() - 30 * 24 * 3600
    result = [
        t for t in tickets
        if not (
            all(r.get("closed") for r in t.get("recipients", {}).values())
            and _ts_to_float(t.get("createdAt", "")) < cutoff
        )
    ]
    return result[-5000:]

def get_deaths_list() -> list:
    result = [{"id": pid, "name": p["name"], "deaths": p.get("deaths", 0)}
              for pid, p in _players.items()]
    result.sort(key=lambda x: x["deaths"], reverse=True)
    return result

# ── WebSocket helpers ──────────────────────────────────────────────────────────
async def ws_broadcast(msg: dict, exclude_id: Optional[str] = None) -> None:
    raw = json.dumps(msg)
    for pid, p in list(_players.items()):
        if pid != exclude_id:
            try:
                await p["ws"].send_text(raw)
            except Exception:
                pass

async def ws_send(ws: WebSocket, msg: dict) -> None:
    try:
        await ws.send_text(json.dumps(msg))
    except Exception:
        pass

# ── App ────────────────────────────────────────────────────────────────────────
app = FastAPI(title="NEXO")
app.add_middleware(CORSMiddleware, allow_origins=["*"],
                   allow_methods=["*"], allow_headers=["*"])

_COMMON_HEADERS = {"Access-Control-Allow-Origin": "*", "ngrok-skip-browser-warning": "true"}
_START_TIME = time.time()

def jres(data: Any, status: int = 200) -> JSONResponse:
    return JSONResponse(content=data, status_code=status, headers=_COMMON_HEADERS)

# ── Ping / Health ──────────────────────────────────────────────────────────────
@app.get("/ping")
async def ping():
    return PlainTextResponse("pong")

@app.get("/health")
async def health():
    return {"status": "ok", "uptime": time.time() - _START_TIME}

# ── Auth ───────────────────────────────────────────────────────────────────────
@app.post("/auth/login")
async def auth_login(request: Request):
    ip = (request.client.host if request.client else "unknown")
    if not check_rate_limit(ip):
        return jres({"error": "Demasiados intentos. Esperá 15 minutos."}, 429)
    try:
        body = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    username = body.get("username", "")
    password = body.get("password", "")
    if not username or not (2 <= len(username) <= 20):
        return jres({"error": "Usuario: 2-20 caracteres"}, 400)
    users = load_users()
    user = next((u for u in users if u["username"].lower() == username.lower()), None)
    if not user or not user.get("passwordHash") or not password \
            or not verify_password(password, user["passwordHash"]):
        record_failed_attempt(ip)
        return jres({"error": "Usuario o contraseña incorrectos"}, 401)
    if not user["passwordHash"].startswith("scrypt:"):
        user["passwordHash"] = hash_password(password)
        save_users(users)
    clear_attempts(ip)
    return jres({"ok": True, "token": create_session(user["username"]), "username": user["username"]})

@app.post("/auth/register")
async def auth_register(request: Request):
    try:
        body = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    username = body.get("username", "")
    password = body.get("password", "")
    if not username or not (2 <= len(username) <= 20):
        return jres({"error": "Usuario: 2-20 caracteres"}, 400)
    if not password:
        return jres({"error": "Se requiere contraseña"}, 400)
    users = load_users()
    if any(u["username"].lower() == username.lower() for u in users):
        return jres({"error": "Ese usuario ya existe"}, 409)
    is_admin = username.lower() == ADMIN_USER
    user = {
        "id": f"u_{int(time.time() * 1000)}",
        "username": username,
        "passwordHash": hash_password(password),
        **({"role": "admin"} if is_admin else {}),
    }
    users.append(user)
    save_users(users)
    return jres({"ok": True, "token": create_session(user["username"]), "username": user["username"]})

@app.post("/auth/logout")
async def auth_logout(request: Request):
    try:
        body = await request.json()
        _sessions.pop(body.get("token", ""), None)
    except Exception:
        pass
    return jres({"ok": True})

@app.get("/auth/check")
async def auth_check(token: Optional[str] = None):
    sess = get_session(token)
    if sess:
        return jres({"ok": True, "username": sess["username"]})
    return jres({"ok": False}, 401)

# ── Upload ─────────────────────────────────────────────────────────────────────
@app.post("/upload")
async def upload_file(request: Request):
    body_bytes = await request.body()
    if len(body_bytes) > 15 * 1024 * 1024:
        return jres({"error": "body too large"}, 400)
    try:
        data = json.loads(body_bytes)
    except Exception:
        return jres({"error": "upload failed"}, 400)
    if not get_session(data.get("token")):
        return jres({"error": "No autorizado"}, 401)
    filename  = data.get("filename", "")
    file_data = data.get("data", "")
    w = data.get("w", 64)
    h = data.get("h", 64)
    if not filename or not file_data:
        return jres({"error": "missing fields"}, 400)
    safe = re.sub(r"[^a-zA-Z0-9._-]", "_", filename)[:80]
    b64  = file_data.split(",")[1] if "," in file_data else file_data
    (UPLOADS_DIR / safe).write_bytes(base64.b64decode(b64))
    meta  = load_uploads_meta()
    entry = {"filename": safe, "src": f"/uploads/{safe}", "w": int(w) or 64, "h": int(h) or 64}
    idx   = next((i for i, m in enumerate(meta) if m["filename"] == safe), -1)
    if idx >= 0:
        meta[idx] = entry
    else:
        meta.append(entry)
    save_uploads_meta(meta)
    return jres({"ok": True, "src": f"/uploads/{safe}", "w": entry["w"], "h": entry["h"]})

@app.get("/uploads-list")
async def uploads_list():
    return jres(load_uploads_meta())

@app.delete("/upload/{filename}")
async def delete_upload(filename: str, request: Request):
    safe = re.sub(r"[^a-zA-Z0-9._-]", "_", filename)
    try:
        body = await request.json()
        if not get_session(body.get("token")):
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    fp = UPLOADS_DIR / safe
    if fp.exists():
        fp.unlink()
    save_uploads_meta([m for m in load_uploads_meta() if m["filename"] != safe])
    return jres({"ok": True})

# ── Map ────────────────────────────────────────────────────────────────────────
@app.post("/map")
async def save_map(request: Request):
    try:
        data = await request.json()
    except Exception:
        return jres({"error": "invalid"}, 400)
    map_token = data.get("token") or request.headers.get("authorization")
    if not get_session(map_token):
        return jres({"error": "No autorizado"}, 401)
    items  = data if isinstance(data, list) else data.get("items", [])
    rooms  = [] if isinstance(data, list) else data.get("rooms", [])
    walls  = [] if isinstance(data, list) else data.get("walls", [])
    payload: dict = {"items": items, "rooms": rooms, "walls": walls}
    if not isinstance(data, list):
        if data.get("worldW"):
            payload["worldW"] = int(data["worldW"])
        if data.get("worldH"):
            payload["worldH"] = int(data["worldH"])
    MAP_FILE.write_text(json.dumps(payload, indent=2), "utf-8")
    reload_rooms()
    return jres({"ok": True})

# ── Worlds ─────────────────────────────────────────────────────────────────────
@app.get("/api/worlds")
async def get_worlds():
    return jres(load_worlds_index())

@app.post("/api/worlds")
async def create_world(request: Request):
    try:
        body = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    if not get_session(body.get("token")):
        return jres({"error": "No autorizado"}, 401)
    name = (body.get("name") or "").strip()
    if not name:
        return jres({"error": "Nombre requerido"}, 400)
    wid      = f"world_{int(time.time() * 1000)}"
    map_data = body.get("data") or {"worldW": 2000, "worldH": 1500, "rooms": [], "walls": [], "floors": [], "items": []}
    _save(world_file(wid), {"name": name, **map_data})
    idx = load_worlds_index()
    idx.append({"id": wid, "name": name, "created": _iso_now()})
    save_worlds_index(idx)
    return jres({"ok": True, "id": wid})

@app.get("/api/worlds/{world_id}")
async def get_world(world_id: str):
    if not re.match(r"^world_\d+$", world_id):
        return jres({"error": "ID de mundo inválido"}, 400)
    wf = world_file(world_id)
    if not wf.exists():
        return jres({"error": "Mundo no encontrado"}, 404)
    data = json.loads(wf.read_text("utf-8"))
    reload_rooms_from_data(data)
    return jres(data)

@app.post("/api/worlds/{world_id}")
async def save_world(world_id: str, request: Request):
    if not re.match(r"^world_\d+$", world_id):
        return jres({"error": "ID de mundo inválido"}, 400)
    try:
        data = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    map_token = data.get("token") or request.headers.get("authorization")
    if not get_session(map_token):
        return jres({"error": "No autorizado"}, 401)
    edited_by = data.pop("editedBy", "?")
    wf       = world_file(world_id)
    existing = json.loads(wf.read_text("utf-8"))
    data["name"] = data.get("name") or existing.get("name")
    _save(wf, data)
    reload_rooms_from_data(data)
    idx   = load_worlds_index()
    entry = next((w for w in idx if w["id"] == world_id), None)
    if entry and data.get("name"):
        entry["name"] = data["name"]
    save_worlds_index(idx)
    asyncio.create_task(ws_broadcast({"type": "map-updated", "worldId": world_id, "mapData": data, "by": edited_by}))
    return jres({"ok": True})

@app.delete("/api/worlds/{world_id}")
async def delete_world(world_id: str, request: Request):
    try:
        body = await request.json()
        if not get_session(body.get("token")):
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    idx = load_worlds_index()
    if len(idx) <= 1:
        return jres({"error": "No podés borrar el último mundo"}, 400)
    save_worlds_index([w for w in idx if w["id"] != world_id])
    wf = world_file(world_id)
    if wf.exists():
        wf.unlink()
    return jres({"ok": True})

@app.patch("/api/worlds/{world_id}/rename")
async def rename_world(world_id: str, request: Request):
    try:
        body = await request.json()
        if not get_session(body.get("token")):
            return jres({"error": "No autorizado"}, 401)
        name = body.get("name")
        if not name:
            return jres({"error": "Nombre requerido"}, 400)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    wf   = world_file(world_id)
    data = json.loads(wf.read_text("utf-8"))
    data["name"] = name
    _save(wf, data)
    idx   = load_worlds_index()
    entry = next((w for w in idx if w["id"] == world_id), None)
    if entry:
        entry["name"] = name
    save_worlds_index(idx)
    return jres({"ok": True})

# ── Users ──────────────────────────────────────────────────────────────────────
@app.get("/api/users/public")
async def get_users_public(token: Optional[str] = None):
    if not get_session(token):
        return jres({"error": "No autorizado"}, 401)
    users = load_users()
    return jres([{"username": u["username"], "role": u.get("role")} for u in users])

@app.get("/api/users")
async def get_users(token: Optional[str] = None):
    sess = get_session(token)
    if not sess:
        return jres({"error": "No autorizado"}, 401)
    users = load_users()
    me = next((u for u in users if u["username"] == sess["username"]), None)
    if not me or me.get("role") != "admin":
        return jres({"error": "Solo admin"}, 403)
    return jres([{"username": u["username"], "role": u.get("role")} for u in users])

@app.delete("/api/users/{username}")
async def delete_user(username: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    users = load_users()
    me = next((u for u in users if u["username"] == sess["username"]), None)
    if not me or me.get("role") != "admin":
        return jres({"error": "Solo admin"}, 403)
    if username == sess["username"]:
        return jres({"error": "No podés borrarte a vos mismo"}, 400)
    idx = next((i for i, u in enumerate(users) if u["username"] == username), -1)
    if idx < 0:
        return jres({"error": "Usuario no encontrado"}, 404)
    users.pop(idx)
    save_users(users)
    for pid, p in list(_players.items()):
        if p["name"] == username:
            asyncio.create_task(ws_send(p["ws"], {"type": "kicked", "reason": "Tu cuenta fue eliminada por un administrador."}))
            _players.pop(pid, None)
            asyncio.create_task(ws_broadcast({"type": "player-left", "id": pid}))
            break
    for tok, s in list(_sessions.items()):
        if s["username"] == username:
            _sessions.pop(tok, None)
    return jres({"ok": True})

@app.patch("/api/users/{username}/role")
async def update_user_role(username: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    users = load_users()
    me = next((u for u in users if u["username"] == sess["username"]), None)
    if not me or me.get("role") != "admin":
        return jres({"error": "Solo admin"}, 403)
    target = next((u for u in users if u["username"] == username), None)
    if not target:
        return jres({"error": "Usuario no encontrado"}, 404)
    role = body.get("role")
    if role not in ["admin", "jefe", "operador", None]:
        return jres({"error": "Rol inválido"}, 400)
    target["role"] = role
    save_users(users)
    asyncio.create_task(ws_broadcast({"type": "role-updated", "username": username, "role": role}))
    return jres({"ok": True})

# ── Tickets ────────────────────────────────────────────────────────────────────
@app.get("/api/tickets")
async def get_tickets(token: Optional[str] = None):
    sess = get_session(token)
    if not sess:
        return jres({"error": "No autorizado"}, 401)
    username = sess["username"]
    tickets  = load_tickets()
    mine = [t for t in tickets
            if t.get("createdBy") == username or username in (t.get("recipients") or {})]
    return jres(mine)

@app.post("/api/tickets")
async def create_ticket(request: Request):
    try:
        body = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    sess = get_session(body.get("token"))
    if not sess:
        return jres({"error": "No autorizado"}, 401)
    title = (body.get("title") or "").strip()
    if not title:
        return jres({"error": "Título requerido"}, 400)
    users          = load_users()
    sender         = sess["username"]
    recipient_mode = body.get("recipientMode", "private")
    target_role    = body.get("targetRole")
    targets        = body.get("targets", [])
    recipients: dict = {}
    if recipient_mode == "all":
        for u in users:
            if u["username"] != sender:
                recipients[u["username"]] = {"seen": False, "closed": False}
    elif recipient_mode == "role" and target_role:
        for u in users:
            if u.get("role") == target_role and u["username"] != sender:
                recipients[u["username"]] = {"seen": False, "closed": False}
    elif recipient_mode == "specific" and isinstance(targets, list):
        usernames = {u["username"] for u in users}
        for t in targets:
            if t != sender and t in usernames:
                recipients[t] = {"seen": False, "closed": False}
    valid_types  = ["documento", "incidente", "tarea", "aviso", "consulta", "otro"]
    ticket_type  = body.get("type", "otro")
    ticket = {
        "id":            f"tkt_{int(time.time() * 1000)}",
        "title":         title[:100],
        "type":          ticket_type if ticket_type in valid_types else "otro",
        "description":   (body.get("description") or "")[:500],
        "link":          (body.get("link") or "")[:300],
        "createdBy":     sender,
        "createdAt":     _iso_now(),
        "recipientMode": recipient_mode,
        "targetRole":    target_role,
        "senderClosed":  False,
        "recipients":    recipients,
    }
    tickets = load_tickets()
    tickets.append(ticket)
    tickets = purge_old_tickets(tickets)
    save_tickets(tickets)
    if ticket["recipientMode"] == "all":
        for pid, p in list(_players.items()):
            if p["name"] in recipients:
                asyncio.create_task(ws_send(p["ws"], {"type": "ticket-new", "ticket": ticket}))
    return jres({"ok": True, "ticket": ticket})

@app.post("/api/tickets/{ticket_id}/seen")
async def ticket_seen(ticket_id: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    username = sess["username"]
    tickets  = load_tickets()
    t = next((tk for tk in tickets if tk["id"] == ticket_id), None)
    if not t:
        return jres({"error": "Ticket no encontrado"}, 404)
    if username not in (t.get("recipients") or {}):
        return jres({"error": "No sos destinatario"}, 403)
    t["recipients"][username]["seen"] = True
    save_tickets(tickets)
    for pid, p in _players.items():
        if p["name"] == t["createdBy"]:
            asyncio.create_task(ws_send(p["ws"], {"type": "ticket-status-update",
                                                   "ticketId": ticket_id, "username": username, "seen": True}))
    return jres({"ok": True})

@app.post("/api/tickets/{ticket_id}/close")
async def ticket_close(ticket_id: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    username = sess["username"]
    tickets  = load_tickets()
    t = next((tk for tk in tickets if tk["id"] == ticket_id), None)
    if not t:
        return jres({"error": "Ticket no encontrado"}, 404)
    if username not in (t.get("recipients") or {}):
        return jres({"error": "No sos destinatario"}, 403)
    t["recipients"][username]["seen"]   = True
    t["recipients"][username]["closed"] = True
    save_tickets(tickets)
    for pid, p in _players.items():
        if p["name"] == t["createdBy"]:
            asyncio.create_task(ws_send(p["ws"], {"type": "ticket-status-update", "ticketId": ticket_id,
                                                   "username": username, "seen": True, "closed": True}))
    all_closed = all(r.get("closed") for r in t.get("recipients", {}).values())
    if all_closed:
        for pid, p in _players.items():
            if p["name"] == t["createdBy"]:
                asyncio.create_task(ws_send(p["ws"], {"type": "ticket-all-closed", "ticketId": ticket_id}))
    return jres({"ok": True})

@app.post("/api/tickets/{ticket_id}/close-sender")
async def ticket_close_sender(ticket_id: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    tickets = load_tickets()
    t = next((tk for tk in tickets if tk["id"] == ticket_id), None)
    if not t:
        return jres({"error": "Ticket no encontrado"}, 404)
    if t["createdBy"] != sess["username"]:
        return jres({"error": "Solo el creador puede cerrar"}, 403)
    t["senderClosed"]   = True
    t["senderClosedAt"] = _iso_now()
    save_tickets(tickets)
    for pid, p in _players.items():
        if p["name"] in (t.get("recipients") or {}):
            asyncio.create_task(ws_send(p["ws"], {"type": "ticket-status-update", "ticketId": ticket_id,
                                                   "senderClosed": True, "senderName": sess["username"]}))
    return jres({"ok": True})

@app.delete("/api/tickets/{ticket_id}")
async def delete_ticket(ticket_id: str, request: Request):
    try:
        body = await request.json()
        sess = get_session(body.get("token"))
        if not sess:
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    users = load_users()
    me    = next((u for u in users if u["username"] == sess["username"]), None)
    tickets = load_tickets()
    t = next((tk for tk in tickets if tk["id"] == ticket_id), None)
    if not t:
        return jres({"error": "Ticket no encontrado"}, 404)
    if t["createdBy"] != sess["username"] and (not me or me.get("role") != "admin"):
        return jres({"error": "Solo el creador o un admin puede borrar"}, 403)
    save_tickets([tk for tk in tickets if tk["id"] != ticket_id])
    return jres({"ok": True})

# ── Widget defaults ────────────────────────────────────────────────────────────
@app.get("/api/widget-defaults")
async def get_widget_defaults():
    return jres({"defaults": load_widget_defaults()})

@app.post("/api/widget-defaults")
async def save_widget_defaults_ep(request: Request):
    body_bytes = await request.body()
    if len(body_bytes) > 64_000:
        return jres({"error": "payload too large"}, 400)
    try:
        data = json.loads(body_bytes)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    sess = get_session(data.get("token"))
    if not sess:
        return jres({"error": "No autorizado"}, 401)
    users = load_users()
    u = next((u for u in users if u["username"] == sess["username"]), None)
    if not u or u.get("role") != "admin":
        return jres({"error": "Solo admins"}, 403)
    layout = data.get("layout")
    if not layout or not isinstance(layout, dict):
        return jres({"error": "layout inválido"}, 400)
    save_widget_defaults(layout)
    print(f"[widgets] default layout guardado por {sess['username']}")
    return jres({"ok": True})

# ── Monitor records ────────────────────────────────────────────────────────────
@app.get("/api/monitor-records")
async def get_monitor_records(token: Optional[str] = None):
    if not get_session(token):
        return jres({"error": "No autorizado"}, 401)
    return jres(load_monitor_records())

@app.post("/api/monitor-records")
async def save_monitor_record(request: Request):
    try:
        rec = await request.json()
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    if not get_session(rec.get("token")):
        return jres({"error": "No autorizado"}, 401)
    if not rec.get("id"):
        return jres({"error": "Sin id"}, 400)
    recs = load_monitor_records()
    idx  = next((i for i, r in enumerate(recs) if r["id"] == rec["id"]), -1)
    if idx >= 0:
        recs[idx] = rec
    else:
        recs.insert(0, rec)
    save_monitor_records(recs)
    asyncio.create_task(ws_broadcast({"type": "monitor-records-updated", "records": recs}))
    return jres({"ok": True})

@app.delete("/api/monitor-records/{record_id}")
async def delete_monitor_record(record_id: str, token: Optional[str] = None):
    if not get_session(token):
        return jres({"error": "No autorizado"}, 401)
    recs = [r for r in load_monitor_records() if r["id"] != record_id]
    save_monitor_records(recs)
    asyncio.create_task(ws_broadcast({"type": "monitor-records-updated", "records": recs}))
    return jres({"ok": True})

# ── Soundboard ─────────────────────────────────────────────────────────────────
@app.get("/api/soundboard")
async def get_soundboard(token: Optional[str] = None):
    if not get_session(token):
        return jres({"error": "No autorizado"}, 401)
    return jres(load_soundboard())

@app.post("/api/soundboard/{slot}")
async def save_soundboard_slot(slot: int, request: Request):
    if slot < 0 or slot > 4:
        return jres({"error": "Slot inválido (0-4)"}, 400)
    body_bytes = await request.body()
    if len(body_bytes) > 80 * 1024 * 1024:
        return jres({"error": "body too large"}, 400)
    try:
        data = json.loads(body_bytes)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    sess = get_session(data.get("token"))
    if not sess:
        return jres({"error": "No autorizado"}, 401)
    file_data = data.get("data", "")
    if not file_data:
        return jres({"error": "Sin audio"}, 400)
    ext      = (data.get("ext") or "").lower()
    safe_ext = ext if ext in ["mp3","wav","ogg","webm","m4a"] else "webm"
    filename = f"sb_{slot}_{int(time.time() * 1000)}.{safe_ext}"
    b64      = file_data.split(",")[1] if "," in file_data else file_data
    board    = load_soundboard()
    if board[slot] and board[slot].get("filename"):
        old = SOUNDS_DIR / board[slot]["filename"]
        if old.exists():
            old.unlink()
    (SOUNDS_DIR / filename).write_bytes(base64.b64decode(b64))
    name  = (data.get("name") or f"Sonido {slot+1}")[:30]
    emoji = (data.get("emoji") or "🔊")[:4]
    board[slot] = {
        "slot": slot, "name": name, "emoji": emoji,
        "filename": filename, "url": f"/uploads/sounds/{filename}",
        "uploadedBy": sess["username"],
    }
    save_soundboard(board)
    asyncio.create_task(ws_broadcast({"type": "soundboard-updated", "board": board}))
    return jres({"ok": True, "board": board})

@app.delete("/api/soundboard/{slot}")
async def delete_soundboard_slot(slot: int, request: Request):
    if slot < 0 or slot > 4:
        return jres({"error": "Slot inválido"}, 400)
    try:
        body = await request.json()
        if not get_session(body.get("token")):
            return jres({"error": "No autorizado"}, 401)
    except Exception:
        return jres({"error": "Datos inválidos"}, 400)
    board = load_soundboard()
    if board[slot] and board[slot].get("filename"):
        old = SOUNDS_DIR / board[slot]["filename"]
        if old.exists():
            old.unlink()
    board[slot] = None
    save_soundboard(board)
    asyncio.create_task(ws_broadcast({"type": "soundboard-updated", "board": board}))
    return jres({"ok": True, "board": board})

# ── Uploads serving (from DATA_DIR volume) ────────────────────────────────────
@app.get("/uploads/{filepath:path}")
async def serve_upload(filepath: str):
    safe      = filepath.replace("..", "").lstrip("/")
    file_path = (UPLOADS_DIR / safe).resolve()
    if not str(file_path).startswith(str(UPLOADS_DIR.resolve())):
        return Response(status_code=403)
    if not file_path.exists():
        return Response(status_code=404)
    media_type = mimetypes.guess_type(str(file_path))[0] or "application/octet-stream"
    return FileResponse(str(file_path), media_type=media_type, headers=_COMMON_HEADERS)

# ── Background music ───────────────────────────────────────────────────────────
@app.get("/bg-music.mp3")
async def bg_music(request: Request):
    sound_dir = BASE_DIR / "sound"
    try:
        files = [f for f in sound_dir.iterdir() if f.suffix == ".mp3"]
    except Exception:
        return Response(status_code=404)
    if not files:
        return Response(status_code=404)
    mp3       = files[0]
    file_size = mp3.stat().st_size
    range_hdr = request.headers.get("range")
    if range_hdr:
        parts = range_hdr.replace("bytes=", "").split("-")
        start = int(parts[0])
        end   = int(parts[1]) if parts[1] else file_size - 1
        def _iter():
            with open(mp3, "rb") as f:
                f.seek(start)
                remaining = end - start + 1
                while remaining > 0:
                    chunk = f.read(min(65536, remaining))
                    if not chunk:
                        break
                    remaining -= len(chunk)
                    yield chunk
        return StreamingResponse(_iter(), status_code=206, headers={
            "Content-Range":  f"bytes {start}-{end}/{file_size}",
            "Accept-Ranges":  "bytes",
            "Content-Length": str(end - start + 1),
            "Content-Type":   "audio/mpeg",
        })
    return FileResponse(str(mp3), media_type="audio/mpeg",
                        headers={"Accept-Ranges": "bytes"})

# ── Panel ──────────────────────────────────────────────────────────────────────
@app.get("/panel")
async def panel():
    if PANEL_FILE.exists():
        return FileResponse(str(PANEL_FILE), media_type="text/html")
    return Response("Panel not found", status_code=404)

# ── WebSocket ──────────────────────────────────────────────────────────────────
@app.websocket("/")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    pid    = str(_next_id[0])
    _next_id[0] += 1
    color  = COLORS[_color_idx[0] % len(COLORS)]
    _color_idx[0] += 1
    joined = False

    try:
        while True:
            try:
                raw = await ws.receive_text()
            except WebSocketDisconnect:
                break
            except Exception:
                break

            try:
                msg = json.loads(raw)
            except Exception:
                continue

            msg_type = msg.get("type")

            # ── join ──────────────────────────────────────────────
            if msg_type == "join":
                if joined:
                    continue
                sess = get_session(str(msg.get("token") or ""))
                if not sess:
                    await ws_send(ws, {"type": "auth-error", "msg": "Sesión vencida. Recargá."})
                    continue
                joined = True
                name   = sess["username"]

                # Kick previous session
                for old_pid, old_p in list(_players.items()):
                    if old_p["name"] == name:
                        await ws_send(old_p["ws"], {"type": "kicked", "reason": "Nueva sesión iniciada en otro lugar."})
                        try:
                            await old_p["ws"].close()
                        except Exception:
                            pass
                        _players.pop(old_pid, None)
                        await ws_broadcast({"type": "player-left", "id": old_pid})
                        print(f"[kick] {name} — sesión anterior terminada")
                        break

                user_record = next((u for u in load_users() if u["username"] == name), None)
                avatar      = validate_avatar(
                    user_record.get("avatar") if user_record else msg.get("avatar")
                )
                avatar["inKart"] = False

                if user_record and user_record.get("position"):
                    pos = user_record["position"]
                    x, y = float(pos.get("x", 1500)), float(pos.get("y", 1390))
                else:
                    import random
                    sp   = random.choice([[1300,1390],[1500,1380],[1700,1390],[1800,1360],[1400,1420]])
                    x    = sp[0] + (random.random() - 0.5) * 40
                    y    = sp[1] + (random.random() - 0.5) * 40

                room_id    = get_room_id(x, y)
                role       = user_record.get("role") if user_record else None
                saved_muted= user_record.get("muted", False) if user_record else False

                _players[pid] = {
                    "ws": ws, "name": name, "x": x, "y": y, "color": color,
                    "avatar": avatar, "sitting": False, "seatX": 0, "seatY": 0,
                    "seatRotation": 0, "roomId": room_id, "role": role,
                    "muted": saved_muted, "hp": MAX_HP, "deaths": 0, "dead": False,
                    "lastAttack": 0.0, "moveCount": 0,
                }

                worlds_idx     = load_worlds_index()
                active_world   = worlds_idx[0]["id"] if worlds_idx else None

                await ws_send(ws, {
                    "type": "state-full", "myId": pid, "myMuted": saved_muted,
                    "userId":       user_record.get("id") if user_record else None,
                    "worldId":      active_world,
                    "soundboard":   load_soundboard(),
                    "widgetDefaults": load_widget_defaults(),
                    "players": [
                        {"id": ppid, "name": pp["name"], "x": pp["x"], "y": pp["y"],
                         "color": pp["color"], "avatar": pp["avatar"], "sitting": pp["sitting"],
                         "seatX": pp["seatX"], "seatY": pp["seatY"], "seatRotation": pp["seatRotation"],
                         "roomId": pp["roomId"], "role": pp["role"], "muted": pp.get("muted", False),
                         "hp": pp.get("hp", MAX_HP), "deaths": pp.get("deaths", 0), "dead": pp.get("dead", False)}
                        for ppid, pp in _players.items()
                    ],
                })
                await ws_send(ws, {"type": "deaths-update", "list": get_deaths_list()})
                await ws_broadcast({"type": "player-joined", "player": {
                    "id": pid, "name": name, "x": x, "y": y, "color": color,
                    "avatar": avatar, "sitting": False, "roomId": room_id,
                    "role": role, "muted": saved_muted,
                }}, pid)

                pending = [t for t in load_tickets()
                           if t.get("recipients") and name in t["recipients"]
                           and not t["recipients"][name].get("closed")]
                if pending:
                    await ws_send(ws, {"type": "tickets-pending", "tickets": pending})

                if room_id and room_id in _room_music:
                    m = _room_music[room_id]
                    await ws_send(ws, {"type": "music-play", "url": m["url"], "name": m["name"]})

                print(f"[+] {name} ({pid}) @ {room_id or 'none'} — total: {len(_players)}")

            # ── move ──────────────────────────────────────────────
            elif msg_type == "move":
                p = _players.get(pid)
                if not p or p["sitting"]:
                    continue
                prev_room = p["roomId"]
                p["x"]    = float(msg.get("x") or p["x"])
                p["y"]    = float(msg.get("y") or p["y"])
                p["roomId"] = get_room_id(p["x"], p["y"])
                await ws_broadcast({"type": "player-moved", "id": pid, "x": p["x"], "y": p["y"]}, pid)
                p["moveCount"] += 1
                if p["moveCount"] % 30 == 0:
                    save_player_position(p["name"], p["x"], p["y"])
                if p["roomId"] != prev_room:
                    await ws_broadcast({"type": "player-room-change", "id": pid, "roomId": p["roomId"]})
                    if prev_room and prev_room in _room_music:
                        await ws_send(ws, {"type": "music-stop"})
                    if p["roomId"] and p["roomId"] in _room_music:
                        m = _room_music[p["roomId"]]
                        await ws_send(ws, {"type": "music-play", "url": m["url"], "name": m["name"]})

            # ── chat ──────────────────────────────────────────────
            elif msg_type == "chat":
                p = _players.get(pid)
                if not p:
                    continue
                img = msg.get("imageData")
                if isinstance(img, str) and len(img) >= 400_000:
                    img = None
                await ws_broadcast({"type": "chat-msg", "id": pid, "name": p["name"], "color": p["color"],
                                    "text": str(msg.get("text") or "")[:200],
                                    "ts": int(time.time() * 1000), "imageData": img})

            # ── speaking ──────────────────────────────────────────
            elif msg_type == "speaking":
                await ws_broadcast({"type": "player-speaking", "id": pid, "value": bool(msg.get("value"))}, pid)

            # ── door-toggle ───────────────────────────────────────
            elif msg_type == "door-toggle":
                if not msg.get("itemId"):
                    continue
                await ws_broadcast({"type": "door-toggle", "itemId": msg["itemId"], "target": msg.get("target")}, pid)

            # ── player-status ─────────────────────────────────────
            elif msg_type == "player-status":
                p = _players.get(pid)
                if not p:
                    continue
                if isinstance(msg.get("muted"), bool):
                    p["muted"] = msg["muted"]
                if isinstance(msg.get("deafened"), bool):
                    p["deafened"] = msg["deafened"]
                await ws_broadcast({"type": "player-status", "id": pid,
                                    "muted": p.get("muted", False), "deafened": p.get("deafened", False)}, pid)
                try:
                    users = load_users()
                    u = next((u for u in users if u["username"] == p["name"]), None)
                    if u:
                        u["muted"] = p.get("muted", False)
                        save_users(users)
                except Exception:
                    pass

            # ── map-update ────────────────────────────────────────
            elif msg_type == "map-update":
                p = _players.get(pid)
                if not p:
                    continue
                w_id = str(msg.get("worldId") or "")
                if not w_id or not re.match(r"^world_\d+$", w_id):
                    continue
                wf = world_file(w_id)
                if not wf.exists():
                    continue
                try:
                    existing = json.loads(wf.read_text("utf-8"))
                    updated  = {**existing, **(msg.get("mapData") or {}), "name": existing.get("name")}
                    _save(wf, updated)
                    await ws_broadcast({"type": "map-updated", "worldId": w_id, "mapData": updated, "by": p["name"]}, pid)
                except Exception as e:
                    print(f"[map-update] {e}")

            # ── avatar-update ─────────────────────────────────────
            elif msg_type == "avatar-update":
                p = _players.get(pid)
                if not p:
                    continue
                p["avatar"] = validate_avatar(msg.get("avatar"))
                await ws_broadcast({"type": "player-avatar", "id": pid, "avatar": p["avatar"]}, pid)
                await ws_send(ws, {"type": "player-avatar", "id": pid, "avatar": p["avatar"]})
                users = load_users()
                for u in users:
                    if u["username"] == p["name"]:
                        u["avatar"] = p["avatar"]
                        save_users(users)
                        break

            # ── sit ───────────────────────────────────────────────
            elif msg_type == "sit":
                p = _players.get(pid)
                if not p:
                    continue
                p["sitting"] = bool(msg.get("sitting"))
                if p["sitting"]:
                    p["x"] = p["seatX"] = float(msg.get("x") or p["x"])
                    p["y"] = p["seatY"] = float(msg.get("y") or p["y"])
                    p["seatRotation"]   = float(msg.get("seatRotation") or 0)
                await ws_broadcast({"type": "player-sit", "id": pid, "sitting": p["sitting"],
                                    "x": p["x"], "y": p["y"], "seatRotation": p.get("seatRotation", 0)}, pid)

            # ── music ─────────────────────────────────────────────
            elif msg_type == "music":
                p   = _players.get(pid)
                if not p:
                    continue
                url = str(msg.get("url") or "")[:300]
                rid = p["roomId"]
                if url:
                    if rid:
                        _room_music[rid] = {"url": url, "name": p["name"]}
                    for pp in _players.values():
                        if pp["roomId"] == rid:
                            await ws_send(pp["ws"], {"type": "music-play", "url": url, "name": p["name"]})
                else:
                    if rid:
                        _room_music.pop(rid, None)
                    for pp in _players.values():
                        if pp["roomId"] == rid:
                            await ws_send(pp["ws"], {"type": "music-stop"})

            # ── wave ──────────────────────────────────────────────
            elif msg_type == "wave":
                p = _players.get(pid)
                if not p:
                    continue
                await ws_broadcast({"type": "player-wave", "id": pid, "name": p["name"]}, pid)

            # ── player-attack ─────────────────────────────────────
            elif msg_type == "player-attack":
                attacker = _players.get(pid)
                if not attacker or attacker.get("dead"):
                    continue
                if attacker.get("avatar", {}).get("inKart"):
                    continue
                now = time.time()
                if now - attacker.get("lastAttack", 0) < ATTACK_COOLDOWN:
                    continue
                attacker["lastAttack"] = now

                facing = msg.get("facing")
                if not isinstance(facing, int) or not (0 <= facing <= 3):
                    facing = int(attacker.get("avatar", {}).get("facing", 0))
                f_angle = FACING_ANGLES[facing]

                closest: Optional[dict] = None
                closest_dist = float("inf")
                for vpid, vp in _players.items():
                    if vpid == pid or vp.get("dead"):
                        continue
                    dx   = vp["x"] - attacker["x"]
                    dy   = vp["y"] - attacker["y"]
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > HIT_RANGE or dist >= closest_dist:
                        continue
                    v_angle = math.atan2(dy, dx)
                    diff    = v_angle - f_angle
                    diff   -= round(diff / (2 * math.pi)) * (2 * math.pi)
                    if abs(diff) > HIT_CONE:
                        continue
                    closest      = {"pid": vpid, "p": vp, "dx": dx, "dy": dy, "dist": dist}
                    closest_dist = dist

                if not closest:
                    continue

                victim    = closest["p"]
                victim_id = closest["pid"]
                length    = closest["dist"] or 1
                kx = (closest["dx"] / length) * KNOCKBACK_DIST
                ky = (closest["dy"] / length) * KNOCKBACK_DIST
                victim["hp"] = victim.get("hp", MAX_HP) - 1

                await ws_broadcast({"type": "player-hit", "attackerId": pid, "victimId": victim_id,
                                    "hp": victim["hp"], "kx": kx, "ky": ky})

                if victim["hp"] <= 0:
                    victim["dead"]   = True
                    victim["deaths"] = victim.get("deaths", 0) + 1
                    await ws_broadcast({"type": "player-died", "victimId": victim_id, "deaths": victim["deaths"]})
                    await ws_broadcast({"type": "deaths-update", "list": get_deaths_list()})

                    async def _respawn(vpid: str = victim_id) -> None:
                        await asyncio.sleep(RESPAWN_DELAY)
                        v = _players.get(vpid)
                        if not v:
                            return
                        v["hp"] = MAX_HP
                        v["dead"] = False
                        v["x"] = COMBAT_SPAWN_X
                        v["y"] = COMBAT_SPAWN_Y
                        await ws_broadcast({"type": "player-respawned", "victimId": vpid,
                                            "x": COMBAT_SPAWN_X, "y": COMBAT_SPAWN_Y, "hp": MAX_HP})

                    asyncio.create_task(_respawn())

            # ── sound-board ───────────────────────────────────────
            elif msg_type == "sound-board":
                p = _players.get(pid)
                if not p:
                    continue
                sound_id = str(msg.get("soundId") or "")[:32]
                url      = str(msg.get("url") or "")[:300]
                if sound_id or url:
                    await ws_broadcast({"type": "sound-board", "soundId": sound_id, "url": url, "from": p["name"]})

            # ── webrtc-signal ─────────────────────────────────────
            elif msg_type == "webrtc-signal":
                target = _players.get(str(msg.get("to") or ""))
                if target:
                    await ws_send(target["ws"], {"type": "webrtc-signal", "from": pid, "signal": msg.get("signal")})

            # ── ticket-seen (WS) ──────────────────────────────────
            elif msg_type == "ticket-seen":
                p = _players.get(pid)
                if not p:
                    continue
                t_id    = str(msg.get("ticketId") or "")
                tickets = load_tickets()
                t       = next((tk for tk in tickets if tk["id"] == t_id), None)
                if not t or p["name"] not in (t.get("recipients") or {}):
                    continue
                t["recipients"][p["name"]]["seen"] = True
                save_tickets(tickets)
                for cp in _players.values():
                    if cp["name"] == t["createdBy"]:
                        await ws_send(cp["ws"], {"type": "ticket-status-update",
                                                  "ticketId": t_id, "username": p["name"], "seen": True})

            # ── ticket-close (WS) ─────────────────────────────────
            elif msg_type == "ticket-close":
                p = _players.get(pid)
                if not p:
                    continue
                t_id    = str(msg.get("ticketId") or "")
                tickets = load_tickets()
                t       = next((tk for tk in tickets if tk["id"] == t_id), None)
                if not t or p["name"] not in (t.get("recipients") or {}):
                    continue
                t["recipients"][p["name"]]["closed"] = True
                save_tickets(tickets)
                for cp in _players.values():
                    if cp["name"] == t["createdBy"]:
                        await ws_send(cp["ws"], {"type": "ticket-status-update",
                                                  "ticketId": t_id, "username": p["name"], "closed": True})
                all_closed = all(r.get("closed") for r in t.get("recipients", {}).values())
                if all_closed:
                    for cp in _players.values():
                        if cp["name"] == t["createdBy"]:
                            await ws_send(cp["ws"], {"type": "ticket-all-closed", "ticketId": t_id})

    except WebSocketDisconnect:
        pass
    except Exception:
        pass
    finally:
        p = _players.pop(pid, None)
        if p:
            print(f"[-] {p['name']} ({pid}) — total: {len(_players)}")
            save_player_position(p["name"], p["x"], p["y"])
            await ws_broadcast({"type": "player-left", "id": pid})

# ── Static files (must be last — catches everything unmatched) ─────────────────
app.mount("/", StaticFiles(directory=str(PUBLIC), html=True), name="static")

# ── Entry point ────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    import socket
    import uvicorn

    hostname = socket.gethostname()
    try:
        lan_ip = socket.gethostbyname(hostname)
    except Exception:
        lan_ip = "localhost"

    print("\n⚡  NEXO (Python/FastAPI)")
    print(f"   Public → {PUBLIC}")
    print(f"   Data   → {DATA_DIR}")
    print(f"   Local  → http://localhost:{PORT}")
    print(f"   LAN   → http://{lan_ip}:{PORT}\n")

    uvicorn.run("server:app", host="0.0.0.0", port=PORT, reload=False)
