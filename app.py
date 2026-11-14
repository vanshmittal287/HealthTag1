"""
HealthTag prototype - Team Schrodinger's, Vivaan-X 2026
A working demo of the three-tier emergency access flow:
  Tier 0  anyone scanning the QR      -> "call 108" + emergency contact number only
  Tier 1  verified doctor/paramedic   -> emergency card, instantly, logged against their credential
  Tier 2  full medical history        -> unlocks only after the emergency contact approves (link or OTP)

Every access is written to an audit log and the owner is notified.
SMS otp delivery is via Fast2SMS (https://www.fast2sms.com/). Set the FAST2SMS_API_KEY environment variable to enable real SMS.
Run with `python app.py`

Environment:
  HEALTHTAG_DEMO=1          seed demo accounts/patient and enable the demo inbox (off by default)
  HEALTHTAG_DATA_DIR        where the database and key files live (keep it OUTSIDE the git repo)
  HEALTHTAG_KEY             Fernet key(s), comma separated: first encrypts, all decrypt (key rotation)
  HEALTHTAG_SECRET_KEY      Flask session-signing secret
  HEALTHTAG_BASE_URL        public URL the QR codes point to (use https:// in production)
  HEALTHTAG_TRUST_PROXY=1   behind a reverse proxy: trust X-Forwarded-For/Proto (needed for rate limits)
  HEALTHTAG_INBOX_OPEN=1    demo only: let non-local machines open /inbox
"""
import hashlib
import io
from flask import send_file
import hmac
import io
import os
import re
import secrets
import socket
import sqlite3
from datetime import datetime, timedelta, timezone
from urllib.parse import urlencode

import requests
from PIL import Image, ImageDraw, ImageFont
from flask import (Flask, Response, abort, flash, g, jsonify, redirect,
                   render_template, request, send_file, session, url_for)
import qrcode
import qrcode.image.svg
from werkzeug.security import check_password_hash, generate_password_hash

APP_DIR = os.path.dirname(os.path.abspath(__file__))
DEMO_MODE = os.environ.get("HEALTHTAG_DEMO", "0") == "1"
DATA_DIR = os.environ.get("HEALTHTAG_DATA_DIR", APP_DIR)
os.makedirs(DATA_DIR, exist_ok=True)
DB_PATH = os.path.join(DATA_DIR, "healthtag.db")
KEY_PATH = os.path.join(DATA_DIR, ".healthtag.key")
SECRET_PATH = os.path.join(DATA_DIR, ".secret_key")
PORT = int(os.environ.get("PORT", 5000))

IST = timezone(timedelta(hours=5, minutes=30))
REQUEST_TTL_MIN = 15      # how long a pending approval request stays valid
ACCESS_TTL_MIN = 30       # how long full-history access lasts once approved
MAX_OTP_ATTEMPTS = 3

# --- rate limits (counted in the database, so they hold across gunicorn workers) ---
LOGIN_MAX_PER_CRED_IP = 5     # failed sign-ins per (ID, IP) in 15 min
LOGIN_MAX_PER_CRED = 20       # failed sign-ins per ID, any IP, in 15 min (high so an attacker can't lock out a real paramedic)
LOGIN_MAX_PER_IP = 30         # failed sign-ins per IP in 15 min
REQ_MAX_PER_PRO_PATIENT = 3   # full-history requests per responder per patient per hour
REQ_MAX_PER_PATIENT = 6       # ... per patient per hour, all responders (protects the contact from SMS spam)
OTP_MAX_WRONG_PER_HOUR = 6    # wrong codes per (responder, patient) per hour, across ALL requests
OWNER_KEY_MAX_PER_IP = 10     # wrong owner keys per IP in 15 min

# --- Fast2SMS (real SMS to the emergency contact) ---
FAST2SMS_API_KEY = os.environ.get("FAST2SMS_API_KEY", "")
FAST2SMS_URL = "https://www.fast2sms.com/dev/bulkV2"
FAST2SMS_ROUTE = os.environ.get("FAST2SMS_ROUTE", "q")   # q = Quick SMS, no DLT
SMS_ENABLED = bool(FAST2SMS_API_KEY)

BLOOD_GROUPS = ["A+", "A-", "B+", "B-", "AB+", "AB-", "O+", "O-", "Not sure"]
TEXT_FIELDS = ["name", "age", "blood_group", "allergies", "conditions", "medications",
               "contact_name", "contact_relation", "contact_phone", "history"]

DEMO_OWNER_KEY = "demo-owner-key"   # fixed so the home page can link the demo patient
DEMO_PROFILE_ID = "AARAV1"


# --------------------------------------------------------------------------- setup
def _load_or_create(path, factory, env_name=None):
    """Env var wins (so secrets can live outside the disk). Otherwise read the file, or create it
    atomically with owner-only permissions (0600)."""
    if env_name and os.environ.get(env_name):
        return os.environ[env_name].strip()
    while True:
        if os.path.exists(path):
            with open(path) as fh:
                return fh.read().strip()
        value = factory()
        try:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        except FileExistsError:      # another worker created it first
            continue
        with os.fdopen(fd, "w") as fh:
            fh.write(value)
        return value


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


# The QR code must point at an address the *phone* can reach, so we use the laptop's
# LAN IP by default. Override with HEALTHTAG_BASE_URL (e.g. an ngrok URL).
BASE_URL = os.environ.get("HEALTHTAG_BASE_URL", f"http://{lan_ip()}:{PORT}").rstrip("/")

app = Flask(__name__)
app.secret_key = _load_or_create(SECRET_PATH, lambda: secrets.token_hex(32), "HEALTHTAG_SECRET_KEY")
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",                    # blocks cross-site form posts (CSRF) until real tokens are added
    SESSION_COOKIE_SECURE=BASE_URL.startswith("https://"),
    PERMANENT_SESSION_LIFETIME=timedelta(hours=8),    # responder and owner sign-ins expire
)
if os.environ.get("HEALTHTAG_TRUST_PROXY") == "1":
    from werkzeug.middleware.proxy_fix import ProxyFix
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)

# Field-level encryption at rest. Optional: falls back to plain text if the
# 'cryptography' package is not installed.
try:
    from cryptography.fernet import Fernet, MultiFernet
    _raw_keys = _load_or_create(KEY_PATH, lambda: Fernet.generate_key().decode(), "HEALTHTAG_KEY")
    # MultiFernet: the first key encrypts, every key can decrypt. This is what makes rotation possible.
    _fernet = MultiFernet([Fernet(k.strip().encode()) for k in _raw_keys.split(",") if k.strip()])
    ENCRYPTED = True
except ImportError:
    if not DEMO_MODE:
        raise RuntimeError("The 'cryptography' package is required outside demo mode (pip install cryptography).")
    _fernet = None
    ENCRYPTED = False


def enc(text):
    text = text or ""
    if not text or _fernet is None:
        return text
    return "enc:" + _fernet.encrypt(text.encode()).decode()


def dec(text):
    if text and text.startswith("enc:") and _fernet is not None:
        try:
            return _fernet.decrypt(text[4:].encode()).decode()
        except Exception:
            return "(unreadable)"
    return text or ""


# --------------------------------------------------------------------------- database
def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
    return g.db


@app.teardown_appcontext
def close_db(_exc):
    conn = g.pop("db", None)
    if conn is not None:
        conn.close()


SCHEMA = """
CREATE TABLE IF NOT EXISTS profiles (
    id TEXT PRIMARY KEY, owner_key TEXT NOT NULL, created_at TEXT NOT NULL,
    name TEXT, age TEXT, blood_group TEXT, allergies TEXT, conditions TEXT, medications TEXT,
    contact_name TEXT, contact_relation TEXT, contact_phone TEXT, history TEXT
);
CREATE TABLE IF NOT EXISTS records (
    id INTEGER PRIMARY KEY AUTOINCREMENT, profile_id TEXT, ts TEXT,
    author TEXT, org TEXT, note TEXT
);
CREATE TABLE IF NOT EXISTS events (
    id INTEGER PRIMARY KEY AUTOINCREMENT, profile_id TEXT, ts TEXT,
    tier INTEGER, actor TEXT, action TEXT, detail TEXT
);
CREATE TABLE IF NOT EXISTS messages (
    id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, profile_id TEXT,
    kind TEXT, to_label TEXT, body TEXT, link TEXT
);
CREATE TABLE IF NOT EXISTS requests (
    id TEXT PRIMARY KEY, profile_id TEXT, ts TEXT, status TEXT, otp TEXT,
    attempts INTEGER DEFAULT 0, requester_cred TEXT, requester_name TEXT, requester_org TEXT,
    decided_at TEXT, decided_by TEXT, decided_via TEXT, approve_hash TEXT
);
CREATE TABLE IF NOT EXISTS professionals (
    cred_id TEXT PRIMARY KEY, name TEXT, org TEXT, pin_hash TEXT
);
CREATE TABLE IF NOT EXISTS attempts (
    id INTEGER PRIMARY KEY AUTOINCREMENT, bucket TEXT, key TEXT, ts TEXT
);
CREATE INDEX IF NOT EXISTS attempts_lookup ON attempts (bucket, key, ts);
"""


def utcnow():
    return datetime.now(timezone.utc)


def iso(dt=None):
    return (dt or utcnow()).isoformat(timespec="seconds")


def parse(value):
    return datetime.fromisoformat(value)


def sha256_hex(text):
    return hashlib.sha256(text.encode()).hexdigest()


def otp_hash(rid, otp):
    """OTPs are stored keyed-hashed, never in plain text."""
    return hmac.new(app.secret_key.encode(), f"{rid}:{otp}".encode(), hashlib.sha256).hexdigest()


def _migrate(conn):
    """Bring a database from an older version up to date."""
    cols = {row[1] for row in conn.execute("PRAGMA table_info(requests)")}
    if "approve_hash" not in cols:
        conn.execute("ALTER TABLE requests ADD COLUMN approve_hash TEXT")
    # Pending requests from before this change have plain-text OTPs and guessable approval links: end them.
    conn.execute("UPDATE requests SET status='expired' WHERE status='pending' AND approve_hash IS NULL")
    # Owner keys used to be stored in plain text; keep only their SHA-256 hash.
    for pid, key in conn.execute("SELECT id, owner_key FROM profiles").fetchall():
        if not re.fullmatch(r"[0-9a-f]{64}", key or ""):
            conn.execute("UPDATE profiles SET owner_key=? WHERE id=?", (sha256_hex(key or secrets.token_hex(16)), pid))


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(SCHEMA)
    _migrate(conn)

    if DEMO_MODE and not conn.execute("SELECT 1 FROM professionals LIMIT 1").fetchone():
        demo_pros = [
            ("H-1001", "Dr. Anita Verma", "Apollo Hospital", "1234"),
            ("A-2002", "Ravi Kumar (paramedic)", "108 Ambulance Service", "1234"),
        ]
        for cred, name, org, pin in demo_pros:
            conn.execute("INSERT INTO professionals VALUES (?,?,?,?)",
                         (cred, name, org, generate_password_hash(pin)))

    if DEMO_MODE and not conn.execute("SELECT 1 FROM profiles LIMIT 1").fetchone():
        demo = {
            "name": "Aarav Sharma", "age": "21", "blood_group": "O+",
            "allergies": "Penicillin, Peanuts",
            "conditions": "Type 1 diabetes",
            "medications": "Insulin (daily)",
            "contact_name": "Neha Sharma", "contact_relation": "Mother",
            "contact_phone": "+919650491090",
            "history": "Appendectomy (2021). Fully vaccinated. Uses an insulin pump; "
                       "carries glucose tablets. No known heart conditions.",
        }
        conn.execute(
            "INSERT INTO profiles (id, owner_key, created_at, " + ", ".join(TEXT_FIELDS) + ") "
            "VALUES (?,?,?," + ",".join("?" * len(TEXT_FIELDS)) + ")",
            (DEMO_PROFILE_ID, sha256_hex(DEMO_OWNER_KEY), iso(), *[enc(demo[f]) for f in TEXT_FIELDS]),
        )
    conn.commit()
    conn.close()


init_db()


# --------------------------------------------------------------------------- helpers
@app.template_filter("ist")
def ist_filter(value):
    try:
        return parse(value).astimezone(IST).strftime("%d %b, %I:%M %p")
    except (TypeError, ValueError):
        return value or ""


@app.template_filter("chips")
def chips_filter(value):
    return [part.strip() for part in re.split(r"[,\n]", value or "") if part.strip()]


@app.context_processor
def inject_globals():
    return {"ENCRYPTED": ENCRYPTED, "BASE_URL": BASE_URL, "pro": current_pro(), "DEMO_MODE": DEMO_MODE}


@app.after_request
def no_store(resp):
    if not request.path.startswith("/static"):
        resp.headers["Cache-Control"] = "no-store"
    resp.headers["Referrer-Policy"] = "no-referrer"        # links with secrets never leak via Referer
    resp.headers["X-Frame-Options"] = "DENY"                # the approval page can't be framed (clickjacking)
    resp.headers["X-Content-Type-Options"] = "nosniff"
    return resp


# ---- rate limiting (database-backed)
def client_ip():
    return request.remote_addr or "unknown"


def hits(bucket, key, minutes):
    cutoff = iso(utcnow() - timedelta(minutes=minutes))
    return db().execute("SELECT COUNT(*) FROM attempts WHERE bucket=? AND key=? AND ts>=?",
                        (bucket, key, cutoff)).fetchone()[0]


def record_hit(bucket, key):
    db().execute("INSERT INTO attempts (bucket, key, ts) VALUES (?,?,?)", (bucket, key, iso()))
    db().execute("DELETE FROM attempts WHERE ts < ?", (iso(utcnow() - timedelta(days=1)),))
    db().commit()


def clear_hits(bucket, key):
    db().execute("DELETE FROM attempts WHERE bucket=? AND key=?", (bucket, key))
    db().commit()


# ---- owner sign-in: the private link is exchanged for a session, then stripped from the URL
def owner_tag(key_hash):
    return key_hash[:16]


def grant_owner(pid, key_hash):
    owned = dict(session.get("owner", {}))
    owned[pid] = owner_tag(key_hash)
    session["owner"] = dict(list(owned.items())[-5:])
    session.permanent = True


def owner_ok(pid, key_hash):
    # The session stores a tag of the key's hash, so rotating the key signs out every other browser.
    return session.get("owner", {}).get(pid) == owner_tag(key_hash)


@app.before_request
def exchange_owner_key():
    supplied = request.values.get("k", "")
    pid = (request.view_args or {}).get("pid")
    if not supplied or not pid:
        return None
    if hits("owner_key", client_ip(), 15) >= OWNER_KEY_MAX_PER_IP:
        abort(429)
    row = db().execute("SELECT owner_key FROM profiles WHERE id=?", (pid,)).fetchone()
    if row and secrets.compare_digest(sha256_hex(supplied).encode(), row["owner_key"].encode()):
        grant_owner(pid, row["owner_key"])
        if request.method == "GET":   # strip ?k= so the secret doesn't stay in history, logs or bookmarks
            rest = [(a, b) for a, b in request.args.items(multi=True) if a != "k"]
            return redirect(request.path + ("?" + urlencode(rest) if rest else ""))
        return None
    record_hit("owner_key", client_ip())
    return None


def load_profile(pid):
    row = db().execute("SELECT * FROM profiles WHERE id=?", (pid,)).fetchone()
    if not row:
        return None
    p = {"id": row["id"], "owner_key": row["owner_key"], "created_at": row["created_at"]}
    for field in TEXT_FIELDS:
        p[field] = dec(row[field])
    return p


def owner_profile(pid):
    """Load a profile for its owner. Auth is the session set by exchange_owner_key(); never the URL."""
    p = load_profile(pid)
    if p is None:
        abort(404)
    if not owner_ok(pid, p["owner_key"]):
        abort(403)
    return p


def log_event(pid, tier, actor, action, detail=""):
    db().execute("INSERT INTO events (profile_id, ts, tier, actor, action, detail) VALUES (?,?,?,?,?,?)",
                 (pid, iso(), tier, actor, action, detail))
    db().commit()


def log_once(pid, tier, actor, action, detail="", minutes=5):
    """Log an event unless the same actor did the same thing very recently (avoids refresh spam)."""
    cutoff = iso(utcnow() - timedelta(minutes=minutes))
    seen = db().execute(
        "SELECT 1 FROM events WHERE profile_id=? AND actor=? AND action=? AND ts>=?",
        (pid, actor, action, cutoff)).fetchone()
    if seen:
        return False
    log_event(pid, tier, actor, action, detail)
    return True

def send_sms(phone, text):
    """Send a real SMS through Fast2SMS. Returns (ok, info). Never raises."""
    if not SMS_ENABLED:
        return False, "SMS off (no FAST2SMS_API_KEY)"
    number = re.sub(r"\D", "", phone or "")[-10:]      # +919800000001 -> 9800000001
    if len(number) != 10:
        return False, "invalid phone number"
    try:
        resp = requests.post(
            FAST2SMS_URL,
            headers={"authorization": FAST2SMS_API_KEY,
                     "Content-Type": "application/json"},
            json={"route": FAST2SMS_ROUTE, "message": text,
                  "numbers": number, "flash": 0},
            timeout=8,
        )
        data = resp.json()
    except (requests.RequestException, ValueError) as exc:
        return False, f"network error: {exc}"
    if data.get("return") is True:
        return True, data.get("request_id", "sent")
    return False, str(data.get("message", data))


def send_message(pid, kind, to_label, body, link="", phone="", inbox_body=None):
    """Inbox entry always; real SMS too when kind == 'contact' and a phone is given.
    The SMS carries `body` (which may include the OTP); the demo inbox shows `inbox_body`
    when given, so one-time codes never appear on the inbox page."""
    if kind == "contact" and phone:
        sms_text = f"{body} {link}".strip()
        ok, info = send_sms(phone, sms_text)
        to_label += " · SMS sent" if ok else f" · SMS not sent ({info})"
    db().execute("INSERT INTO messages (ts, profile_id, kind, to_label, body, link) VALUES (?,?,?,?,?,?)",
                 (iso(), pid, kind, to_label, inbox_body if inbox_body is not None else body, ""))
    db().commit()


def notify_owner(pid, body):
    send_message(pid, "owner", "Owner (HealthTag app)", body)


def current_pro():
    return session.get("pro")


def require_pro():
    pro = current_pro()
    if not pro:
        abort(403)
    return pro


def actor_label(pro):
    return f"{pro['name']}, {pro['org']}"


# ---- access requests
def refresh_request(row):
    """Expire a pending request that has waited too long."""
    if row and row["status"] == "pending" and utcnow() - parse(row["ts"]) > timedelta(minutes=REQUEST_TTL_MIN):
        db().execute("UPDATE requests SET status='expired' WHERE id=?", (row["id"],))
        db().commit()
        row = db().execute("SELECT * FROM requests WHERE id=?", (row["id"],)).fetchone()
    return row


def get_request(rid):
    row = db().execute("SELECT * FROM requests WHERE id=?", (rid,)).fetchone()
    return refresh_request(row)


def latest_pending(pid, cred):
    row = db().execute(
        "SELECT * FROM requests WHERE profile_id=? AND requester_cred=? AND status='pending' "
        "ORDER BY ts DESC LIMIT 1", (pid, cred)).fetchone()
    return refresh_request(row)


def full_access_until(pid):
    """Return when the current professional's full-history access ends, or None."""
    pro = current_pro()
    if not pro:
        return None
    row = db().execute(
        "SELECT decided_at FROM requests WHERE profile_id=? AND requester_cred=? AND status='approved' "
        "ORDER BY decided_at DESC LIMIT 1", (pid, pro["cred"])).fetchone()
    if not row:
        return None
    until = parse(row["decided_at"]) + timedelta(minutes=ACCESS_TTL_MIN)
    return iso(until) if until > utcnow() else None


def decide_request(r, approved, by, via):
    status = "approved" if approved else "denied"
    cur = db().execute("UPDATE requests SET status=?, decided_at=?, decided_by=?, decided_via=? "
                       "WHERE id=? AND status='pending'", (status, iso(), by, via, r["id"]))
    db().commit()
    if cur.rowcount == 0:      # already decided or expired: a request can be decided exactly once
        return
    p = load_profile(r["profile_id"])
    who = f"{r['requester_name']}, {r['requester_org']}"
    how = "using the one-time code" if via == "otp" else "from the approval link"
    if approved:
        log_event(p["id"], 2, by, "approved full history access", f"For {who} ({how})")
        notify_owner(p["id"], f"{by} approved full history access for {who} {how}. "
                              f"Access lasts {ACCESS_TTL_MIN} minutes.")
        send_message(p["id"], "contact", f"{p['contact_name']} ({p['contact_phone']})",
                     f"HealthTag: you approved {who}. They can see {p['name']}'s medical history "
                     f"(past conditions, notes and hospital records) for {ACCESS_TTL_MIN} minutes.",
                     phone=p["contact_phone"])
    else:
        log_event(p["id"], 2, by, "denied full history access", f"Request from {who}")
        notify_owner(p["id"], f"Full history access for {who} was denied ({by}).")


# --------------------------------------------------------------------------- QR
def qr_svg(data):
    factory = qrcode.image.svg.SvgPathImage
    img = qrcode.make(data, image_factory=factory, box_size=10)
    return img.to_string(encoding="unicode")

@app.route("/qr/<pid>.svg")
def qr_image(pid):
    if load_profile(pid) is None:
        abort(404)
    return Response(qr_svg(f"{BASE_URL}/scan/{pid}"), mimetype="image/svg+xml")

@app.route("/qr/<pid>.png")
def qr_png(pid):
    p = load_profile(pid)
    if p is None:
        abort(404)

    # 1. Generate the base QR code
    qr = qrcode.QRCode(
        version=1,
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=10,
        border=2,
    )
    qr.add_data(f"{BASE_URL}/scan/{pid}")
    qr.make(fit=True)
    qr_img = qr.make_image(fill_color="#0B2545", back_color="#FFFFFF").convert("RGBA")

    # 2. Canvas dimensions
    card_w = 480
    card_h = 600
    canvas = Image.new("RGBA", (card_w, card_h), (255, 255, 255, 255))
    draw = ImageDraw.Draw(canvas)

    # 3. Outer border
    draw.rounded_rectangle([(10, 10), (card_w - 10, card_h - 10)], radius=18, outline="#CBD5E1", width=3)

    # 4. Top Emergency Alert Banner
    draw.rounded_rectangle([(10, 10), (card_w - 10, 80)], radius=16, fill="#DC2626")
    # Clean bottom corners of the banner so it merges with the white card
    draw.rectangle([(10, 50), (card_w - 10, 80)], fill="#DC2626")

    # Fonts (uses Pillow's built-in default font; works on all Linux/PythonAnywhere servers without file paths)
    font = ImageFont.load_default()

    # Draw Emergency Header Text
    header_text = "SCAN IN CASE OF MEDICAL EMERGENCY"
    h_box = draw.textbbox((0, 0), header_text, font=font)
    h_w = h_box[2] - h_box[0]
    draw.text(((card_w - h_w) / 2, 40), header_text, fill="#FFFFFF", font=font)

    # 5. Paste QR code in the center
    qr_w, qr_h = qr_img.size
    qr_x = (card_w - qr_w) // 2
    qr_y = 100
    canvas.paste(qr_img, (qr_x, qr_y), qr_img)

    # 6. Bottom Patient ID and Instructions
    code_text = f"PATIENT ID: {pid}"
    c_box = draw.textbbox((0, 0), code_text, font=font)
    c_w = c_box[2] - c_box[0]
    draw.text(((card_w - c_w) / 2, qr_y + qr_h + 15), code_text, fill="#0B2545", font=font)

    sub_text = "Instant 108 Alert & Emergency Contacts"
    s_box = draw.textbbox((0, 0), sub_text, font=font)
    s_w = s_box[2] - s_box[0]
    draw.text(((card_w - s_w) / 2, qr_y + qr_h + 38), sub_text, fill="#64748B", font=font)

    # 7. Export as PNG
    buf = io.BytesIO()
    canvas.convert("RGB").save(buf, format="PNG")
    buf.seek(0)

    as_attachment = request.args.get("download") == "1"
    return send_file(
        buf,
        mimetype="image/png",
        as_attachment=as_attachment,
        download_name=f"HealthTag_{pid}.png"
    )


# --------------------------------------------------------------------------- pages: home, register, card
@app.route("/")
def home():
    return render_template("home.html", demo_id=DEMO_PROFILE_ID, demo_key=DEMO_OWNER_KEY)


def read_profile_form():
    limits = {"history": 2000}
    data = {f: request.form.get(f, "").strip()[:limits.get(f, 300)] for f in TEXT_FIELDS}
    errors = []
    if not data["name"]:
        errors.append("Enter the person's name.")
    if data["blood_group"] not in BLOOD_GROUPS:
        errors.append("Choose a blood group, or 'Not sure'.")
    if not data["contact_name"]:
        errors.append("Enter the emergency contact's name.")
    phone = re.sub(r"[^\d+]", "", data["contact_phone"])
    if len(re.sub(r"\D", "", phone)) < 10:
        errors.append("Enter a valid emergency contact phone number (at least 10 digits).")
    data["contact_phone"] = phone
    return data, errors


@app.route("/register", methods=["GET", "POST"])
def register():
    form = {f: "" for f in TEXT_FIELDS}
    if request.method == "POST":
        form, errors = read_profile_form()
        if errors:
            for e in errors:
                flash(e)
        else:
            pid = secrets.token_urlsafe(5).replace("-", "x").replace("_", "y").upper()
            key = secrets.token_urlsafe(16)
            db().execute(
                "INSERT INTO profiles (id, owner_key, created_at, " + ", ".join(TEXT_FIELDS) + ") "
                "VALUES (?,?,?," + ",".join("?" * len(TEXT_FIELDS)) + ")",
                (pid, sha256_hex(key), iso(), *[enc(form[f]) for f in TEXT_FIELDS]))
            db().commit()
            log_event(pid, 0, "Owner", "created this HealthTag")
            grant_owner(pid, sha256_hex(key))
            session["reveal"] = {"pid": pid, "k": key}      # shown once on the card page, then dropped
            return redirect(url_for("card", pid=pid))
    return render_template("profile_form.html", form=form, editing=False, blood_groups=BLOOD_GROUPS)


@app.route("/card/<pid>")
def card(pid):
    p = owner_profile(pid)
    recovery = None
    reveal = session.get("reveal")
    if reveal and reveal.get("pid") == pid:
        session.pop("reveal", None)
        recovery = f"{BASE_URL}/owner/{pid}?k={reveal['k']}"
    return render_template("card.html", p=p, recovery=recovery)


@app.post("/owner/<pid>/rotate-key")
def owner_rotate_key(pid):
    """Issue a new private link. The old link and every other browser's owner session stop working."""
    p = owner_profile(pid)
    key = secrets.token_urlsafe(16)
    db().execute("UPDATE profiles SET owner_key=? WHERE id=?", (sha256_hex(key), pid))
    db().commit()
    log_event(pid, 0, "Owner", "created a new private link", "The previous link no longer works")
    grant_owner(pid, sha256_hex(key))
    session["reveal"] = {"pid": pid, "k": key}
    return redirect(url_for("card", pid=pid))


@app.route("/owner/<pid>")
def owner(pid):
    p = owner_profile(pid)
    events = db().execute("SELECT * FROM events WHERE profile_id=? ORDER BY id DESC LIMIT 60", (pid,)).fetchall()
    notes = db().execute("SELECT * FROM messages WHERE profile_id=? AND kind='owner' ORDER BY id DESC LIMIT 30",
                         (pid,)).fetchall()
    records = db().execute("SELECT * FROM records WHERE profile_id=? ORDER BY id DESC", (pid,)).fetchall()
    records = [dict(r, note=dec(r["note"])) for r in records]
    return render_template("owner.html", p=p, events=events, notes=notes, records=records)


@app.route("/owner/<pid>/edit", methods=["GET", "POST"])
def owner_edit(pid):
    p = owner_profile(pid)
    form = {f: p[f] for f in TEXT_FIELDS}
    if request.method == "POST":
        form, errors = read_profile_form()
        if errors:
            for e in errors:
                flash(e)
        else:
            sets = ", ".join(f"{f}=?" for f in TEXT_FIELDS)
            db().execute(f"UPDATE profiles SET {sets} WHERE id=?", (*[enc(form[f]) for f in TEXT_FIELDS], pid))
            db().commit()
            log_event(pid, 0, "Owner", "updated the profile")
            return redirect(url_for("owner", pid=pid))
    return render_template("profile_form.html", form=form, editing=True, p=p, blood_groups=BLOOD_GROUPS)


# --------------------------------------------------------------------------- scanning
@app.route("/scan/<pid>")
def scan(pid):
    p = load_profile(pid)
    if p is None:
        abort(404)
    pro = current_pro()

    # Tier 0: anyone without a verified professional login
    if not pro:
        log_once(pid, 0, "Unverified scanner", "scanned the QR code",
                 "Saw only the emergency alert and contact number", minutes=2)
        return render_template("scan_public.html", p=p)

    # Tier 1: verified professional
    actor = actor_label(pro)
    if log_once(pid, 1, actor, "viewed the emergency card", f"Credential {pro['cred']}"):
        notify_owner(pid, f"{actor} viewed your emergency card.")

    until = full_access_until(pid)
    records = []
    if until:
        rows = db().execute("SELECT * FROM records WHERE profile_id=? ORDER BY id DESC", (pid,)).fetchall()
        records = [dict(r, note=dec(r["note"])) for r in rows]
        log_once(pid, 2, actor, "viewed the full history", f"Credential {pro['cred']}", minutes=5)
    pending = latest_pending(pid, pro["cred"]) if not until else None
    return render_template("scan_pro.html", p=p, until=until, records=records, pending=pending,
                           added=request.args.get("added"))


@app.post("/scan/<pid>/request")
def request_full_history(pid):
    pro = require_pro()
    p = load_profile(pid) or abort(404)
    existing = latest_pending(pid, pro["cred"])
    if existing:
        return redirect(url_for("request_wait", rid=existing["id"]))

    pair = f"{pro['cred']}:{pid}"
    if (hits("req", pair, 60) >= REQ_MAX_PER_PRO_PATIENT or hits("req_patient", pid, 60) >= REQ_MAX_PER_PATIENT
            or hits("otp", pair, 60) >= OTP_MAX_WRONG_PER_HOUR):
        log_event(pid, 2, actor_label(pro), "full history request blocked", "Too many recent requests or wrong codes")
        flash("Too many requests for this person. Wait a while, or call the emergency contact directly.")
        return redirect(url_for("scan", pid=pid))
    record_hit("req", pair)
    record_hit("req_patient", pid)

    rid = secrets.token_urlsafe(8)             # the responder's handle: it appears in THEIR URLs
    token = secrets.token_urlsafe(24)          # the contact's approval secret: sent only to the contact
    otp = f"{secrets.randbelow(10 ** 6):06d}"
    db().execute("INSERT INTO requests (id, profile_id, ts, status, otp, requester_cred, requester_name, requester_org, "
                 "approve_hash) VALUES (?,?,?,?,?,?,?,?,?)",
                 (rid, pid, iso(), "pending", otp_hash(rid, otp), pro["cred"], pro["name"], pro["org"], sha256_hex(token)))
    db().commit()

    actor = actor_label(pro)
    log_event(pid, 2, actor, "requested the full history", f"Waiting for {p['contact_name']} to approve")
    send_message(pid, "contact", f"{p['contact_name']} ({p['contact_phone']})",
             f"HealthTag: {actor} wants {p['name']}'s history. Code: {otp}. Approve/deny:",
             link=f"{BASE_URL}/approve/{token}",
             phone=p["contact_phone"],
             inbox_body=f"HealthTag: {actor} wants {p['name']}'s history. Approve/deny:")
    notify_owner(pid, f"{actor} requested your full history. Waiting for {p['contact_name']} to approve.")
    return redirect(url_for("request_wait", rid=rid))


@app.post("/scan/<pid>/record")
def add_record(pid):
    pro = require_pro()
    load_profile(pid) or abort(404)
    note = request.form.get("note", "").strip()[:1000]
    if note:
        db().execute("INSERT INTO records (profile_id, ts, author, org, note) VALUES (?,?,?,?,?)",
                     (pid, iso(), pro["name"], pro["org"], enc(note)))
        db().commit()
        log_event(pid, 1, actor_label(pro), "added a record", "Visible in the full history")
        notify_owner(pid, f"{actor_label(pro)} added a note to your record.")
    return redirect(url_for("scan", pid=pid, added=1))


# --------------------------------------------------------------------------- request waiting (professional side)
def own_request_or_403(rid):
    pro = require_pro()
    r = get_request(rid)
    if r is None:
        abort(404)
    if r["requester_cred"] != pro["cred"]:
        abort(403)
    return r


@app.route("/request/<rid>")
def request_wait(rid):
    r = own_request_or_403(rid)
    if r["status"] == "approved":
        return redirect(url_for("scan", pid=r["profile_id"]))
    p = load_profile(r["profile_id"])
    return render_template("request_wait.html", r=r, p=p, error=request.args.get("err"),
                           ttl=REQUEST_TTL_MIN, max_attempts=MAX_OTP_ATTEMPTS)


@app.route("/request/<rid>/status")
def request_status(rid):
    r = own_request_or_403(rid)
    return jsonify(status=r["status"], next=url_for("scan", pid=r["profile_id"]))


@app.post("/request/<rid>/otp")
def request_otp(rid):
    r = own_request_or_403(rid)
    if r["status"] != "pending":
        return redirect(url_for("request_wait", rid=rid))
    p = load_profile(r["profile_id"])
    code = re.sub(r"\D", "", request.form.get("otp", ""))
    pair = f"{r['requester_cred']}:{r['profile_id']}"
    if hits("otp", pair, 60) >= OTP_MAX_WRONG_PER_HOUR:       # new requests don't reset the guess budget
        decide_request(r, False, "Locked after too many wrong codes", "otp")
        return redirect(url_for("request_wait", rid=rid))
    if secrets.compare_digest(otp_hash(rid, code), r["otp"]):
        decide_request(r, True, f"{p['contact_name']} (code read out)", "otp")
        return redirect(url_for("scan", pid=r["profile_id"]))
    record_hit("otp", pair)
    attempts = r["attempts"] + 1
    db().execute("UPDATE requests SET attempts=? WHERE id=?", (attempts, rid))
    db().commit()
    if attempts >= MAX_OTP_ATTEMPTS:
        decide_request(r, False, "Locked after 3 wrong codes", "otp")
        return redirect(url_for("request_wait", rid=rid))
    return redirect(url_for("request_wait", rid=rid, err=MAX_OTP_ATTEMPTS - attempts))


# --------------------------------------------------------------------------- emergency contact approval
@app.route("/approve/<token>", methods=["GET", "POST"])
def approve(token):
    """The token is sent only to the emergency contact. The responder never sees it, so they can't self-approve."""
    row = db().execute("SELECT id FROM requests WHERE approve_hash=?", (sha256_hex(token),)).fetchone()
    if row is None:
        abort(404)
    rid = row["id"]
    r = get_request(rid)
    if r is None:
        abort(404)
    p = load_profile(r["profile_id"])
    if request.method == "POST" and r["status"] == "pending":
        approved = request.form.get("decision") == "approve"
        decide_request(r, approved, p["contact_name"], "link")
        r = get_request(rid)
    return render_template("contact_approve.html", r=r, p=p)


# --------------------------------------------------------------------------- professional sign-in
DUMMY_PIN_HASH = generate_password_hash("not-a-real-pin")


def safe_next(value):
    ok = value and value.startswith("/") and not value.startswith("//") and "\\" not in value
    return value if ok else url_for("home")


@app.route("/pro/login", methods=["GET", "POST"])
def pro_login():
    nxt = safe_next(request.values.get("next", ""))
    if request.method == "POST":
        cred = request.form.get("cred", "").strip().upper()
        pin = request.form.get("pin", "")
        ip = client_ip()
        if (hits("login_cred_ip", f"{cred}|{ip}", 15) >= LOGIN_MAX_PER_CRED_IP
                or hits("login_cred", cred, 15) >= LOGIN_MAX_PER_CRED
                or hits("login_ip", ip, 15) >= LOGIN_MAX_PER_IP):
            flash("Too many failed sign-ins. Wait 15 minutes and try again.")
            return render_template("pro_login.html", nxt=nxt), 429
        row = db().execute("SELECT * FROM professionals WHERE cred_id=?", (cred,)).fetchone()
        # Always run one hash check so unknown IDs and wrong PINs take the same time.
        pin_ok = check_password_hash(row["pin_hash"] if row else DUMMY_PIN_HASH, pin)
        if row and pin_ok:
            clear_hits("login_cred_ip", f"{cred}|{ip}")
            session["pro"] = {"cred": row["cred_id"], "name": row["name"], "org": row["org"]}
            session.permanent = True
            return redirect(nxt)
        record_hit("login_cred_ip", f"{cred}|{ip}")
        record_hit("login_cred", cred)
        record_hit("login_ip", ip)
        flash("That ID and PIN don't match a verified professional.")
    return render_template("pro_login.html", nxt=nxt)


@app.route("/pro/logout")
def pro_logout():
    session.pop("pro", None)
    return redirect(safe_next(request.args.get("next", "")))


# --------------------------------------------------------------------------- demo inbox
def inbox_allowed():
    """Demo only, and only from the presenter's own machine. A request that came through a tunnel or proxy
    carries X-Forwarded-For, so it is never treated as local. HEALTHTAG_INBOX_OPEN=1 lifts the local-only rule."""
    if not DEMO_MODE:
        return False
    if os.environ.get("HEALTHTAG_INBOX_OPEN") == "1":
        return True
    return request.remote_addr in ("127.0.0.1", "::1") and "X-Forwarded-For" not in request.headers


@app.route("/inbox")
def inbox():
    if not inbox_allowed():
        abort(404)
    messages = db().execute("SELECT * FROM messages WHERE kind='contact' ORDER BY id DESC LIMIT 40").fetchall()
    return render_template("inbox.html", messages=messages)


@app.post("/inbox/clear")
def inbox_clear():
    if not inbox_allowed():
        abort(404)
    db().execute("DELETE FROM messages WHERE kind='contact'")
    db().commit()
    return redirect(url_for("inbox"))


# --------------------------------------------------------------------------- errors
@app.errorhandler(403)
def forbidden(_e):
    return render_template("error.html", title="Access denied",
                           text="This page needs a verified sign-in or the owner's private link."), 403


@app.errorhandler(429)
def too_many(_e):
    return render_template("error.html", title="Too many attempts",
                           text="Please wait a few minutes before trying again."), 429


@app.errorhandler(404)
def not_found(_e):
    return render_template("error.html", title="Not found",
                           text="This HealthTag or page doesn't exist."), 404


if __name__ == "__main__":
    if DEMO_MODE:
        with app.app_context():  # start every demo session with an empty inbox
            db().execute("DELETE FROM messages WHERE kind='contact'")
            db().commit()
    print("\n  HealthTag prototype")
    print(f"  Open on this laptop : http://localhost:{PORT}")
    print(f"  Phones (same Wi-Fi) : {BASE_URL}   <- QR codes point here")
    print(f"  Field encryption    : {'on' if ENCRYPTED else 'OFF (pip install cryptography to enable)'}")
    print(f"  Demo mode           : {'ON (seed data + local inbox)' if DEMO_MODE else 'off'}\n")
    # Outside demo mode listen on localhost only; put a TLS-terminating reverse proxy in front.
    app.run(host="0.0.0.0" if DEMO_MODE else "127.0.0.1", port=PORT, debug=False)
