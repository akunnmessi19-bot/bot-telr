"""Bot Telegram toko nomor virtual - SMSCode API v1 (IDR). Python 3.10+ / aiogram 3."""
import asyncio, base64, re, hashlib, hmac, html, io, json, logging, math, os, random, shutil, sqlite3, tempfile, time, uuid
from datetime import datetime, timedelta, timezone
from urllib.parse import quote as urlquote
import aiohttp, aiosqlite, qrcode
from aiohttp import web
from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (BufferedInputFile, CallbackQuery, FSInputFile, InlineKeyboardButton,
                           InlineKeyboardMarkup, Message)

load_dotenv()
try:
    BOT_TOKEN = os.environ["BOT_TOKEN"]
    SMS_TOKEN = os.environ["SMSCODE_TOKEN"]
except KeyError as e:
    raise SystemExit(f"Variabel {e} belum diisi (BOT_TOKEN & SMSCODE_TOKEN wajib ada di .env / Variables).")
ADMINS = {int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip()}
MARKUP = float(os.getenv("MARKUP_PERCENT", "30"))
STORE = os.getenv("STORE_NAME", "OTP Store")
PAY_INFO = os.getenv("PAYMENT_INFO", "Hubungi admin untuk metode pembayaran.").replace("\\n", "\n")
MIN_DEP = int(os.getenv("MIN_DEPOSIT", "2000"))
_vol = os.getenv("RAILWAY_VOLUME_MOUNT_PATH", "").strip()          # otomatis diisi Railway kalau service punya Volume
DB_PATH = os.getenv("DB_PATH") or (os.path.join(_vol, "store.db") if _vol else "store.db")   # prioritas: DB_PATH > Volume > folder kerja
AUTO_CANCEL = int(os.getenv("AUTO_CANCEL_MIN", "10")) * 60
KASERA_KEY = os.getenv("KASERA_API_KEY", "")          # kp_test_... atau kp_live_...
WH_SECRET = os.getenv("KASERA_WEBHOOK_SECRET", "")    # signing secret endpoint webhook
WEBHOOK_PORT = int(os.getenv("WEBHOOK_PORT") or os.getenv("PORT") or 8080)   # Railway otomatis mengisi PORT
FEE_PCT_BPS = round(float(os.getenv("KASERA_FEE_PERCENT", "0.7")) * 100)     # QRIS Kasera 0,7% (dalam basis poin)
FEE_FIXED = int(os.getenv("KASERA_FEE_FIXED", "250"))                        # QRIS Kasera + Rp250
LIVE = KASERA_KEY.startswith("kp_live_")
API = "https://api.smscode.gg/v1"
LINE = "<code>────────────────────</code>"
PRIORITY = ["whatsapp", "telegram", "shopee", "tiktok", "instagram", "facebook", "google", "gojek", "grab"]
TITLE = os.getenv("START_TITLE", "UMKM OTP - VIRTUAL NUMBER STORE")
BANNER_FILE = os.getenv("BANNER_FILE", "robot_banner.jpg")   # taruh file ini di folder yang sama dengan bot.py
_c = os.getenv("CHANNEL_ID", "").strip()                     # contoh: -1001234567890
CHANNEL_ID = int(_c) if _c.lstrip("-").isdigit() else (_c or None)
CHANNEL_URL = os.getenv("CHANNEL_URL", "").strip()           # link channel (opsional, untuk tombol di menu)
# ===== WAJIB JOIN CHANNEL =====
# Isi dengan username channel (contoh: "@umkmotp") atau ID (contoh: "-1001234567890").
# Bot WAJIB dijadikan admin di channel tsb. Kosongkan ("") untuk mematikan fitur wajib join.
gateway_channel = os.getenv("GATEWAY_CHANNEL", "").strip()
gateway_channel_url = os.getenv("GATEWAY_CHANNEL_URL", "").strip()   # opsional, link undangan untuk channel privat
PER_PAGE = 7
REF_PERCENT = float(os.getenv("REF_PERCENT", "5"))          # komisi referral (% dari harga order yang OTP-nya masuk)
REF_MIN_WD = int(os.getenv("REF_MIN_WD", "5000"))            # minimal penarikan saldo referral
REF_GOPAY_FEE = int(os.getenv("REF_GOPAY_FEE", "1000"))      # biaya admin tarik ke GoPay
WD_CHANNEL_ID = os.getenv("WD_CHANNEL_ID", "").strip()       # tujuan laporan penarikan: ID numerik (-100...) atau @username channel publik
WD_CHANNEL_URL = os.getenv("WD_CHANNEL_URL", "").strip()     # opsional; dipakai hanya jika WD_CHANNEL_ID kosong (hanya bisa dibaca bila link publik / t.me/c/<id>/..)
SR_MIN = 5                                                   # minimal transaksi agar SR ditampilkan
PRIO_COUNTRIES = ["PH", "ID", "BR", "CL", "ZA"]              # selalu di atas pada halaman 1
EXACT_30 = {"BR", "CL"}                                      # harga jual = modal x 1.30 persis
BANNER_ID = None
try:
    from aiogram.types import CopyTextButton
except ImportError:  # aiogram lama: tombol salin diganti popup
    CopyTextButton = None

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("otpbot")
r = Router()
db: aiosqlite.Connection
http: aiohttp.ClientSession


# ---------- helpers ----------
def rp(n): return "Rp. " + f"{int(n):,}".replace(",", ".")
def esc(s): return html.escape(str(s))
def sell_price(cost, country=None):
    code = str((country or {}).get("code", "")).upper()
    if code in EXACT_30:  # Brazil & Chile: modal x 1.30 persis, tanpa pembulatan
        return (int(cost) * 130 + 50) // 100
    return int(math.ceil(cost * (1 + MARKUP / 100) / 100) * 100)
def b(t, d): return InlineKeyboardButton(text=t, callback_data=d)
def kb(rows): return InlineKeyboardMarkup(inline_keyboard=rows)


def pager(items, page, make, nav):
    """List 1 kolom, PER_PAGE item per halaman, tombol Sebelumnya/Selanjutnya."""
    page = max(0, min(page, max(0, (len(items) - 1) // PER_PAGE)))
    rows = [[make(i)] for i in items[page * PER_PAGE:(page + 1) * PER_PAGE]]
    row = []
    if page > 0: row.append(b("⬅️ Sebelumnya", f"{nav}:{page - 1}"))
    if (page + 1) * PER_PAGE < len(items): row.append(b("Selanjutnya ➔", f"{nav}:{page + 1}"))
    if row: rows.append(row)
    return rows


async def show(cb: CallbackQuery, text, markup=None):
    """Edit pesan di tempat (tidak dihapus). Pesan berfoto -> edit caption."""
    try:
        if cb.message.photo:
            await cb.message.edit_caption(caption=text, reply_markup=markup)
        else:
            await cb.message.edit_text(text, reply_markup=markup)
    except TelegramBadRequest as e:
        if "not modified" not in str(e):
            log.warning("show gagal: %s", e)


# ---------- database ----------
async def fetch(sql, args=()):
    cur = await db.execute(sql, args)
    return [dict(x) for x in await cur.fetchall()]

async def one(sql, args=()):
    rows = await fetch(sql, args)
    return rows[0] if rows else None

async def run(sql, args=()):
    cur = await db.execute(sql, args)
    await db.commit()
    return cur.rowcount

async def init_db():
    await db.executescript("""
    CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, name TEXT, balance INTEGER DEFAULT 0, joined REAL);
    CREATE TABLE IF NOT EXISTS orders(id INTEGER PRIMARY KEY, user_id INTEGER, label TEXT, phone TEXT,
        price INTEGER, status TEXT, otp TEXT, rev INTEGER DEFAULT 0, chat_id INTEGER, msg_id INTEGER,
        created REAL, refunded INTEGER DEFAULT 0);
    CREATE TABLE IF NOT EXISTS deposits(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
        amount INTEGER, total INTEGER, status TEXT DEFAULT 'PENDING', created REAL);
    CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
    CREATE TABLE IF NOT EXISTS referrals(referred_id INTEGER PRIMARY KEY, referrer_id INTEGER, created REAL);
    CREATE INDEX IF NOT EXISTS idx_ref_referrer ON referrals(referrer_id);
    CREATE TABLE IF NOT EXISTS ref_commissions(order_id INTEGER PRIMARY KEY, referrer_id INTEGER, referred_id INTEGER,
        amount INTEGER, created REAL);
    CREATE TABLE IF NOT EXISTS withdrawals(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, amount INTEGER,
        method TEXT, account TEXT, holder TEXT, fee INTEGER DEFAULT 0, status TEXT DEFAULT 'PENDING', created REAL);
    """)
    for tbl, col in [("deposits", "kasera_id TEXT"), ("orders", "sid INTEGER"), ("orders", "cid INTEGER"), ("orders", "oid INTEGER"),
                     ("orders", "svc TEXT"), ("orders", "ctry TEXT"), ("orders", "code TEXT"), ("orders", "msg TEXT"),
                     ("orders", "ph INTEGER"), ("users", "ref_balance INTEGER DEFAULT 0"), ("withdrawals", "chan_msg INTEGER")]:
        try:
            await db.execute(f"ALTER TABLE {tbl} ADD COLUMN {col}")
        except Exception:
            pass  # kolom sudah ada
    await db.commit()

async def balance(uid, name=""):
    await run("INSERT OR IGNORE INTO users(id,name,joined) VALUES(?,?,?)", (uid, name, time.time()))
    return (await one("SELECT balance FROM users WHERE id=?", (uid,)))["balance"]

async def deduct(uid, amt):
    return await run("UPDATE users SET balance=balance-? WHERE id=? AND balance>=?", (amt, uid, amt)) > 0

async def credit(uid, amt):
    await run("UPDATE users SET balance=balance+? WHERE id=?", (amt, uid))

async def refund(oid, status):
    """Kembalikan saldo pengguna tepat satu kali."""
    if await run("UPDATE orders SET refunded=1,status=? WHERE id=? AND refunded=0", (status, oid)) == 0:
        return None
    o = await one("SELECT * FROM orders WHERE id=?", (oid,))
    await credit(o["user_id"], o["price"])
    return o


# ---------- SMSCode API ----------
async def api(method, path, headers=None, **kw):
    try:
        async with http.request(method, API + path, headers={"Authorization": f"Bearer {SMS_TOKEN}", **(headers or {})},
                                timeout=aiohttp.ClientTimeout(total=20), **kw) as resp:
            j = await resp.json()
    except Exception as e:
        log.warning("API %s %s gagal: %s", method, path, e)
        return None, "NETWORK"
    if j.get("success"):
        return j["data"], None
    return None, j.get("error", {}).get("code", "ERROR")

_cache = {}
async def cached(path, params=None, ttl=300):
    key = (path, tuple(sorted((params or {}).items())))
    t, v = _cache.get(key, (0, None))
    if v is not None and time.time() - t < ttl:
        return v
    d, _ = await api("GET", path, params=params)
    if d is not None:
        _cache[key] = (time.time(), d)
    return d or []

async def offers(sid, cid, oid=0):
    """Penawaran nomor untuk layanan+negara (+operator), termurah dulu."""
    params = {"country_id": cid, "platform_id": sid, "sort": "price_asc", "limit": 200}
    if int(oid): params["operator_id"] = oid
    d, _ = await api("GET", "/catalog/products", params=params)
    ok = [p for p in (d or []) if p.get("active") and p.get("available", 0) > 0]
    return sorted(ok, key=lambda p: (p.get("price", 0), p.get("id", 0)))

async def country_stats(sid):
    """Per negara untuk satu layanan: harga modal termurah + total stok."""
    best = {}
    for p in await cached("/catalog/products", {"platform_id": sid, "sort": "price_asc", "limit": 10000}, ttl=20):
        if not (p.get("active") and p.get("available", 0) > 0): continue
        c = best.setdefault(p["country_id"], {"price": p["price"], "stock": 0})
        c["price"] = min(c["price"], p["price"]); c["stock"] += p["available"]
    return best

async def sr_stats(sid):
    """Success rate (OTP masuk) dari transaksi toko sendiri, 14 hari terakhir."""
    rows = await fetch("SELECT cid, COUNT(*) n, SUM(CASE WHEN otp IS NOT NULL THEN 1 ELSE 0 END) s FROM orders "
                       "WHERE sid=? AND cid IS NOT NULL AND created>? AND (status!='ACTIVE' OR created<?) GROUP BY cid",
                       (int(sid), time.time() - 14 * 86400, time.time() - AUTO_CANCEL))
    return {x["cid"]: round(100 * (x["s"] or 0) / x["n"]) for x in rows if x["n"] >= SR_MIN}

async def svc_name(sid):
    return next((s["name"] for s in await cached("/catalog/services", ttl=600) if str(s["id"]) == str(sid)), "Layanan")

async def country_of(cid):
    return next((c for c in await cached("/catalog/countries", ttl=600) if str(c["id"]) == str(cid)), {})

async def op_name(sid, cid, oid):
    if not int(oid): return "Semua operator"
    ops = await cached("/catalog/operators", {"country_id": cid, "platform_id": sid}, ttl=120)
    return next((o["name"] for o in ops if str(o.get("operator_id")) == str(oid)), "Operator")


# ---------- tampilan ----------
_banner = None
def _font(size):
    from PIL import ImageFont
    for p in ("/usr/share/fonts/truetype/dejavu/DejaVuSerif-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"):
        try: return ImageFont.truetype(p, size)
        except Exception: pass
    try: return ImageFont.load_default(size=size)
    except TypeError: return ImageFont.load_default()

def banner():
    """Banner hitam-emas dibuat otomatis, tidak butuh file gambar."""
    global _banner
    if _banner: return _banner
    from PIL import Image, ImageDraw
    W, H = 1000, 420
    gold, dim, soft = (212, 175, 55), (122, 100, 34), (225, 225, 232)
    img = Image.new("RGB", (W, H))
    d = ImageDraw.Draw(img)
    for y in range(H):
        c = int(12 + 20 * y / H)
        d.line([(0, y), (W, y)], fill=(c, c, c + 5))
    d.rectangle([16, 16, W - 16, H - 16], outline=gold, width=3)
    d.rectangle([28, 28, W - 28, H - 28], outline=dim, width=1)
    cx = W // 2
    def center(text, y, size, fill):
        f = _font(size)
        while d.textlength(text, font=f) > W - 140 and size > 24:
            size -= 4; f = _font(size)
        d.text(((W - d.textlength(text, font=f)) / 2, y), text, font=f, fill=fill)
    def diamond(x, y, r, fill):
        d.polygon([(x, y - r), (x + r, y), (x, y + r), (x - r, y)], fill=fill)
    diamond(cx, 84, 22, gold)
    center(STORE.upper(), 128, 70, gold)
    d.line([(cx - 190, 238), (cx - 24, 238)], fill=dim, width=2)
    d.line([(cx + 24, 238), (cx + 190, 238)], fill=dim, width=2)
    diamond(cx, 238, 8, gold)
    center("PREMIUM VIRTUAL NUMBER", 262, 30, soft)
    center("INSTAN   •   AMAN   •   24 JAM", 332, 22, dim)
    buf = io.BytesIO()
    img.save(buf, "PNG")
    _banner = buf.getvalue()
    return _banner

def menu_kb():
    rows = [[b("📱 Beli Nomor Virtual", "sv:0")],
            [b("💳 Top Up Saldo", "dep"), b("👤 Akun Saya", "me")],
            [b("📜 Riwayat", "hist"), b("🛟 Bantuan", "help")],
            [b("🎁 Referral", "ref")]]
    if CHANNEL_URL:
        rows.append([InlineKeyboardButton(text="📡 Live OTP Channel", url=CHANNEL_URL)])
    return kb(rows)

def welcome(name, bal):
    n = esc(name)
    return (f"📱 <b>{esc(TITLE)}</b>\n\n"
            f"Halo <b>{n}</b>, selamat datang!\n"
            f"Layanan penyedia nomor kosong (nokos) otomatis untuk berbagai keperluan verifikasi OTP.\n\n"
            f"👤 Akun: <code>{n}</code>\n💵 Saldo: <b>{rp(bal)}</b>\n\n"
            f"⚡️ <i>Keunggulan Kami:</i>\n• Stok nomor melimpah &amp; fresh\n• Masuk otomatis detik itu juga\n"
            f"• Garansi / refund jika kode tidak masuk\n\n🔽 <i>Pilih menu transaksi di bawah ini:</i>")

async def send_home(msg, name, uid):
    """Kirim banner robot + sambutan (send_photo). file_id disimpan agar tidak upload ulang."""
    global BANNER_ID
    bal = await balance(uid, name)
    try:
        sent = await msg.answer_photo(banner_photo(), caption=welcome(name, bal), reply_markup=menu_kb())
        BANNER_ID = sent.photo[-1].file_id
    except Exception:
        BANNER_ID = None
        log.exception("banner gagal, kirim teks biasa")
        await msg.answer(welcome(name, bal), reply_markup=menu_kb())

def banner_photo():
    """Sumber banner robot yang sama untuk menu dan kartu nomor aktif."""
    if BANNER_ID:
        return BANNER_ID
    if os.path.exists(BANNER_FILE):
        return FSInputFile(BANNER_FILE)
    return BufferedInputFile(base64.b64decode(BANNER_B64), "robot_banner.jpg")


STATUS = {"ACTIVE": "🟢 Menunggu kode OTP...", "OTP": "🟢 Kode OTP diterima", "COMPLETED": "✅ Selesai",
          "CANCELED": "❌ Dibatalkan · saldo kembali", "EXPIRED": "❌ Kedaluwarsa · saldo kembali"}
EMOJI = {"ACTIVE": "🟡", "OTP": "🟢", "COMPLETED": "✅", "CANCELED": "❌", "EXPIRED": "❌"}

def cancel_notice(o, price, title, reason):
    """Kartu notifikasi pesanan gagal / OTP tidak masuk (tampilan premium)."""
    where = o.get("svc") or o.get("label") or "-"
    if o.get("ctry"): where += f" ({o['ctry']})"
    jam = datetime.now(timezone(timedelta(hours=7))).strftime("%d/%m/%Y · %H:%M WIB")
    return (f"❌ <b>{title}</b>\n{LINE}\n"
            f"<blockquote>🧾 Pesanan  <b>#{o['id']}</b>\n"
            f"📞 Nomor  <code>{esc(o.get('phone') or '-')}</code>\n"
            f"🏢 Layanan  <b>{esc(where)}</b>\n"
            f"📌 Status  <b>❌ Gagal</b></blockquote>\n"
            f"💸 <b>REFUND OTOMATIS</b>\n"
            f"<blockquote>💰 Dikembalikan  <b>+{rp(price)}</b>\n"
            f"🕒 Waktu  {jam}</blockquote>\n"
            f"ℹ️ <i>{reason}</i>\n"
            f"✨ <i>Saldo sudah kembali utuh, silakan coba nomor lain.</i>")

def cancel_kb(o):
    rows = []
    if o.get("sid") and o.get("cid"):
        rows.append([b("🛒 Beli Lagi", f"rb:{o['id']}")])
    rows.append([b("🏠 Menu Utama", "hm")])
    return kb(rows)

def copy_btn(text, value, oid, kind):
    if CopyTextButton:
        return InlineKeyboardButton(text=text, copy_text=CopyTextButton(text=str(value)))
    return b(text, f"cp:{oid}:{kind}")

def sms_text(o):
    t = f"✉️ <b>SMS MASUK #{o['rev']}</b>\n"
    if o.get("code"): t += f"🔑 KODE OTP: <code>{esc(o['code'])}</code>\n"
    if o.get("msg"): t += f"💬 Pesan: \"{esc(str(o['msg'])[:300])}\""
    elif not o.get("code"): t += f"🔑 KODE OTP: <code>{esc(o['otp'])}</code>"
    return t

def card(o):
    where = o.get("svc") or o["label"]
    if o.get("ctry"): where += f" ({o['ctry']})"
    t = (f"📱 <b>DETAIL NOMOR AKTIF #{o['id']}</b>\n{LINE}\n"
         f"📞 Nomor: <code>{esc(o['phone'])}</code>\n🏢 Layanan: {esc(where)}\n💰 Tarif: {rp(o['price'])}\n\n"
         f"{STATUS[o['status']]}")
    if o.get("otp"):
        t += f"\n\n{LINE}\n" + sms_text(o)
    if o["status"] in ("ACTIVE", "OTP"):
        t += "\n\n💡 <i>Catatan: Jika OTP sudah masuk, jangan langsung klik <b>✅ Selesai / Batal</b> karena kode bisa keluar lebih dari 1 kali kalo lagi hoki.</i>"
    return t
  
def card_kb(o):
    i = o["id"]
    if o["status"] in ("ACTIVE", "OTP"):
        top = [copy_btn("📋 Salin Nomor", o["phone"], i, "n")]
        if o.get("code"): top.append(copy_btn("🔑 Salin OTP", o["code"], i, "o"))
        rows = [top, [b("🔄 Minta SMS Baru", f"rs:{i}"), b("✅ Selesai / Batal", f"en:{i}")]]
        if o.get("sid") and o.get("cid"):
            rows.append([b("🛒 Beli Lagi", f"rb:{i}")])
        return kb(rows)
    rows = []
    if o.get("sid") and o.get("cid"):
        rows += [[b("🛒 Beli Lagi", f"rb:{i}")],
                 [b("🔙 Kembali ke Daftar Nomor", f"of:{o['sid']}:{o['cid']}:{o.get('oid') or 0}:0")]]
    rows.append([b("🏠 Menu Utama", "home")])
    return kb(rows)

async def refresh_card(bot, o):
    try:
        if o.get("ph"):
            await bot.edit_message_caption(chat_id=o["chat_id"], message_id=o["msg_id"], caption=card(o), reply_markup=card_kb(o))
        else:
            await bot.edit_message_text(card(o), chat_id=o["chat_id"], message_id=o["msg_id"], reply_markup=card_kb(o))
    except TelegramBadRequest as e:
        if "not modified" not in str(e):
            log.warning("refresh_card gagal: %s", e)


# ---------- wajib join channel ----------
async def is_joined(bot: Bot, uid):
    if not gateway_channel or uid in ADMINS:
        return True
    try:
        m = await bot.get_chat_member(gateway_channel, uid)
        return m.status in ("member", "administrator", "creator", "restricted")
    except Exception as e:
        log.warning("cek join gateway_channel gagal: %s", e)
        return True   # jangan kunci user kalau bot belum admin / channel salah

def join_url():
    if gateway_channel_url: return gateway_channel_url
    c = str(gateway_channel)
    return f"https://t.me/{c.lstrip('@')}" if c.startswith("@") else None

def join_text(name, failed=False):
    t = (f"🔒 <b>AKSES TERKUNCI</b>\n{LINE}\n"
         f"Halo <b>{esc(name)}</b>! 👋\n\n"
         f"<blockquote>📢 Untuk menggunakan bot ini, kamu wajib join channel resmi kami terlebih dahulu.\n\n"
         f"1️⃣ Klik <b>📢 Join Channel</b>\n2️⃣ Setelah join, klik <b>🔄 Refresh / Sudah Join</b></blockquote>")
    if failed:
        t += "\n❌ <b>Kamu belum terdeteksi join.</b> Silakan join dulu lalu tekan refresh."
    return t

def join_kb():
    rows = []
    if (u := join_url()):
        rows.append([InlineKeyboardButton(text="📢 Join Channel", url=u)])
    rows.append([b("🔄 Refresh / Sudah Join", "jc")])
    return kb(rows)

class JoinGate:
    async def __call__(self, handler, event, data):
        u = getattr(event, "from_user", None)
        if not u or (isinstance(event, CallbackQuery) and event.data == "jc"):
            return await handler(event, data)
        if isinstance(event, Message) and event.chat.type == "private" and (event.text or "").startswith("/start"):
            try:
                await register_ref(u.id, event.text)   # dicatat dulu, supaya tidak hilang walau user tertahan gerbang join
            except Exception:
                log.exception("catat referral gagal")
        if isinstance(event, Message) and event.chat.type != "private":
            return await handler(event, data)
        if await is_joined(data["bot"], u.id):
            return await handler(event, data)
        if isinstance(event, CallbackQuery):
            await event.answer("🔒 Join channel dulu ya!", show_alert=True)
            await event.message.answer(join_text(u.full_name), reply_markup=join_kb())
        else:
            await event.answer(join_text(u.full_name), reply_markup=join_kb())

r.message.outer_middleware(JoinGate())
r.callback_query.outer_middleware(JoinGate())

@r.callback_query(F.data == "jc")
async def join_check(cb: CallbackQuery, bot: Bot, state: FSMContext):
    if not await is_joined(bot, cb.from_user.id):
        await cb.answer("❌ Kamu belum join channel.", show_alert=True)
        try:
            await cb.message.edit_text(join_text(cb.from_user.full_name, True), reply_markup=join_kb())
        except TelegramBadRequest:
            pass
        return
    await cb.answer("✅ Terima kasih sudah join!", show_alert=True)
    try:
        await cb.message.edit_text(f"✅ <b>VERIFIKASI BERHASIL</b>\n{LINE}\n<blockquote>🎉 Kamu sudah join channel. Selamat menggunakan bot!</blockquote>")
    except TelegramBadRequest:
        pass
    await state.clear()
    await send_home(cb.message, cb.from_user.full_name, cb.from_user.id)


# ---------- menu utama ----------
@r.message(CommandStart())
async def start(m: Message, state: FSMContext):
    await state.clear()
    await send_home(m, m.from_user.full_name, m.from_user.id)

@r.callback_query(F.data == "home")
async def home(cb: CallbackQuery):
    """Kembali ke menu dengan edit caption banner (tanpa hapus pesan)."""
    await cb.answer()
    if cb.message.photo:
        bal = await balance(cb.from_user.id, cb.from_user.full_name)
        await show(cb, welcome(cb.from_user.full_name, bal), menu_kb())
    else:
        await send_home(cb.message, cb.from_user.full_name, cb.from_user.id)

@r.callback_query(F.data == "hm")
async def home_new(cb: CallbackQuery):
    """Dari pesan invoice/QR: kirim menu baru lalu rapikan pesan invoice."""
    await cb.answer()
    await send_home(cb.message, cb.from_user.full_name, cb.from_user.id)
    try:
        await cb.message.delete()
    except TelegramBadRequest:
        pass

@r.callback_query(F.data == "me")
async def me(cb: CallbackQuery):
    await cb.answer()
    bal = await balance(cb.from_user.id, cb.from_user.full_name)
    n = (await one("SELECT COUNT(*) c FROM orders WHERE user_id=?", (cb.from_user.id,)))["c"]
    await show(cb, f"👤 <b>AKUN SAYA</b>\n{LINE}\n<blockquote>🆔 ID  <code>{cb.from_user.id}</code>\n"
                   f"Saldo  <b>{rp(bal)}</b>\n🧾 Total pesanan  <b>{n}</b></blockquote>",
               kb([[b("💳 Top Up Saldo", "dep")], [b("🏠 Menu Utama", "home")]]))

DEP_ST = {"OK": "✅ Berhasil", "PENDING": "⏳ Menunggu", "REJECTED": "❌ Ditolak",
          "FAILED": "❌ Gagal", "EXPIRED": "❌ Kedaluwarsa"}

def _tgl(ts):
    return datetime.fromtimestamp(ts or 0, timezone(timedelta(hours=7))).strftime("%d/%m/%y %H:%M")

def hist_kb(active):
    return kb([[b("• 🛒 Pesanan", "hist"), b("💳 Riwayat Top Up", "histd")],
               [b("🏠 Menu Utama", "home")]])

async def show_any(cb: CallbackQuery, text, markup=None):
    """Seperti show(), tapi kalau teks terlalu panjang untuk caption foto (>1024), kirim sebagai pesan baru."""
    if cb.message.photo and len(text) > 1000:
        try:
            await cb.message.edit_reply_markup(reply_markup=None)
        except TelegramBadRequest:
            pass
        return await cb.message.answer(text, reply_markup=markup)
    await show(cb, text, markup)

@r.callback_query(F.data == "hist")
async def hist(cb: CallbackQuery):
    await cb.answer()
    uid = cb.from_user.id
    rows = await fetch("SELECT * FROM orders WHERE user_id=? ORDER BY created DESC LIMIT 8", (uid,))
    st = await one("SELECT COUNT(*) n, SUM(CASE WHEN status IN ('COMPLETED','OTP') THEN 1 ELSE 0 END) ok, "
                   "SUM(CASE WHEN status IN ('CANCELED','EXPIRED') THEN 1 ELSE 0 END) bad, "
                   "COALESCE(SUM(CASE WHEN refunded=0 THEN price ELSE 0 END),0) spent FROM orders WHERE user_id=?", (uid,))
    items = []
    for o in rows:
        where = o.get("svc") or o["label"]
        if o.get("ctry"): where += f" ({o['ctry']})"
        line = (f"{EMOJI[o['status']]} <b>#{o['id']}</b> · {rp(o['price'])}\n"
                f"   🏢 {esc(where)}\n   📞 <code>{esc(o['phone'])}</code>")
        if o.get("code"): line += f"\n   🔑 OTP <code>{esc(o['code'])}</code>"
        line += f"\n   🕒 {_tgl(o['created'])} · {STATUS[o['status']].split(' · ')[0]}"
        items.append(line)
    body = "\n\n".join(items) or "<i>Belum ada pesanan.</i>"
    await show_any(cb, f"📜 <b>RIWAYAT PESANAN</b>\n{LINE}\n"
                   f"<blockquote>📊 Total  <b>{st['n'] or 0}</b>   ✅ <b>{st['ok'] or 0}</b>   ❌ <b>{st['bad'] or 0}</b>\n"
                   f"💸 Total belanja  <b>{rp(st['spent'] or 0)}</b></blockquote>\n"
                   f"<blockquote expandable>{body}</blockquote>\n<i>Menampilkan 8 pesanan terakhir.</i>", hist_kb("o"))

@r.callback_query(F.data == "histd")
async def hist_dep(cb: CallbackQuery):
    await cb.answer()
    uid = cb.from_user.id
    rows = await fetch("SELECT * FROM deposits WHERE user_id=? ORDER BY created DESC LIMIT 8", (uid,))
    st = await one("SELECT COUNT(*) n, SUM(CASE WHEN status='OK' THEN 1 ELSE 0 END) ok, "
                   "SUM(CASE WHEN status IN ('REJECTED','FAILED','EXPIRED') THEN 1 ELSE 0 END) bad, "
                   "COALESCE(SUM(CASE WHEN status='OK' THEN amount ELSE 0 END),0) tot FROM deposits WHERE user_id=?", (uid,))
    items = []
    for d in rows:
        stt = DEP_ST.get(d["status"], d["status"])
        items.append(f"{stt.split(' ')[0]} <b>#{d['id']}</b> · <b>+{rp(d['amount'])}</b>\n"
                     f"   💳 Dibayar {rp(d['total'] or d['amount'])}\n"
                     f"   🕒 {_tgl(d['created'])} · {stt.split(' ', 1)[1]}")
    body = "\n\n".join(items) or "<i>Belum ada riwayat top up.</i>"
    await show_any(cb, f"💳 <b>RIWAYAT TOP UP</b>\n{LINE}\n"
                   f"<blockquote>📊 Total  <b>{st['n'] or 0}</b>   ✅ <b>{st['ok'] or 0}</b>   ❌ <b>{st['bad'] or 0}</b>\n"
                   f"💰 Total saldo masuk  <b>{rp(st['tot'] or 0)}</b></blockquote>\n"
                   f"<blockquote expandable>{body}</blockquote>\n<i>Menampilkan 8 top up terakhir.</i>",
               kb([[b("• 💳 Top Up", "histd"), b("🛒 Pesanan", "hist")],
                   [b("➕ Top Up Sekarang", "dep")], [b("🏠 Menu Utama", "home")]]))

@r.callback_query(F.data == "help")
async def help_(cb: CallbackQuery):
    await cb.answer()
    await show(cb, f"🛟 <b>BANTUAN</b>\n{LINE}\n<blockquote>1️⃣ Top up saldo\n2️⃣ Pilih layanan &amp; negara\n"
                   f"3️⃣ Gunakan nomor di aplikasi tujuan\n4️⃣ Kode OTP muncul otomatis di sini</blockquote>\n"
                   f"♻️ <i>OTP tidak masuk? Pesanan dibatalkan otomatis dan saldo kembali.</i>",
               kb([[b("🏠 Menu Utama", "home")]]))


# ---------- referral (komisi per OTP sukses + penarikan) ----------
# User A bagikan link t.me/<bot>?start=ref_<id A>. User B (BARU) membuka link -> tercatat sebagai teman A.
# Tiap order B yang OTP-nya masuk -> A dapat REF_PERCENT% dari harga order ke SALDO REFERRAL (sekali per order).
# Saldo referral dicairkan lewat penarikan manual (admin setujui/tolak).
_BOT_USER = None

class Wd(StatesGroup):
    form = State()

async def bot_username(bot: Bot):
    global _BOT_USER
    if not _BOT_USER:
        _BOT_USER = (await bot.me()).username
    return _BOT_USER

async def ref_bal(uid):
    await balance(uid)
    return (await one("SELECT COALESCE(ref_balance,0) b FROM users WHERE id=?", (uid,)))["b"]

async def register_ref(uid, text):
    """Catat pengajak dari payload /start. Hanya user baru; pengajak pertama yang dipakai."""
    parts = (text or "").split(maxsplit=1)
    if len(parts) < 2: return
    p = parts[1].strip().lower()
    for pre in ("ref_", "ref"):
        if p.startswith(pre):
            p = p[len(pre):]
            break
    if not p.isdigit(): return
    ref = int(p)
    if ref == uid: return
    if await one("SELECT 1 x FROM users WHERE id=?", (uid,)): return          # sudah pernah pakai bot = bukan user baru
    if not await one("SELECT 1 x FROM users WHERE id=?", (ref,)): return       # pengajak harus user bot ini
    await run("INSERT OR IGNORE INTO referrals(referred_id,referrer_id,created) VALUES(?,?,?)", (uid, ref, time.time()))

async def ref_commission(bot: Bot, o):
    """Dipanggil saat OTP masuk. Komisi dicatat per order (idempotent) lalu masuk ke saldo referral pengajak."""
    rf = await one("SELECT referrer_id FROM referrals WHERE referred_id=?", (o["user_id"],))
    if not rf: return
    amt = int(o["price"] * REF_PERCENT / 100)
    if amt <= 0: return
    cur = await db.execute("INSERT OR IGNORE INTO ref_commissions(order_id,referrer_id,referred_id,amount,created) VALUES(?,?,?,?,?)",
                           (o["id"], rf["referrer_id"], o["user_id"], amt, time.time()))
    await db.commit()
    if cur.rowcount == 0: return                                               # order ini sudah pernah dikomisikan
    await run("UPDATE users SET ref_balance=COALESCE(ref_balance,0)+? WHERE id=?", (amt, rf["referrer_id"]))
    try:
        await bot.send_message(rf["referrer_id"],
                               f"💰 <b>KOMISI REFERRAL</b>\n{LINE}\n<blockquote>Teman kamu berhasil membeli nokos "
                               f"({rp(o['price'])}).\nKomisi <b>+{rp(amt)}</b> masuk ke saldo referral.</blockquote>")
    except Exception:
        log.warning("gagal kirim notifikasi komisi ke %s", rf["referrer_id"])

def ref_text(link, st, bal, friends, more):
    body = "\n".join(friends) or "<i>Belum ada teman yang diundang.</i>"
    return (f"👥 <b>PROGRAM REFERRAL BOT NOKOS</b> 👥\n\n"
            f"Mau dapat penghasilan tambahan? Cukup bagikan link referral Anda dan dapatkan keuntungan dari setiap "
            f"transaksi teman yang Anda undang!\n\n"
            f"💰 <b>Komisi Anda: {REF_PERCENT:g}%</b> dari total harga belanja teman (Real-Time per OTP Sukses!)\n"
            f"<i>Contoh: Teman Anda beli nokos seharga {rp(10000)}, Anda LANGSUNG dapat {rp(10000 * REF_PERCENT / 100)}!</i>\n\n"
            f"🔗 <b>Link Referral Anda:</b>\n<code>{link}</code>\n\n"
            f"📊 <b>Statistik Anda:</b>\n"
            f"• Total Teman Diundang: <b>{st['friends']}</b> orang\n"
            f"• Total Transaksi Sukses: <b>{st['trx']}</b> kali\n"
            f"• Saldo Referral Saat Ini: <b>{rp(bal)}</b>\n\n"
            f"💳 <b>KETENTUAN WITHDRAW (PENARIKAN):</b>\n"
            f"1. Minimal penarikan saldo adalah {rp(REF_MIN_WD)}\n"
            f"2. Penarikan diproses secara MANUAL oleh admin untuk menjamin keamanan &amp; potongan biaya termurah.\n"
            f"3. Metode Penarikan:\n"
            f"   • Tarik Jadi Saldo Bot (GRATIS / Tanpa Potongan Admin)\n"
            f"   • Tarik Ke DANA (GRATIS Biaya Admin!)\n"
            f"   • Tarik Ke GoPay (Biaya Admin {rp(REF_GOPAY_FEE)})\n\n"
            f"👇 Silakan klik tombol di bawah ini jika saldo Anda sudah mencukupi. Penarikan diproses dalam 1-24 jam.\n\n"
            f"👥 <b>Daftar Teman:</b>\n<blockquote expandable>{body}{more}</blockquote>")

@r.callback_query(F.data == "ref")
async def referral(cb: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await cb.answer()
    uid = cb.from_user.id
    bal = await ref_bal(uid)
    link = f"https://t.me/{await bot_username(bot)}?start=ref_{uid}"
    st = {"friends": (await one("SELECT COUNT(*) c FROM referrals WHERE referrer_id=?", (uid,)))["c"],
          "trx": (await one("SELECT COUNT(*) c FROM ref_commissions WHERE referrer_id=?", (uid,)))["c"]}
    rows = await fetch("SELECT r.referred_id id, u.name, "
                       "(SELECT COUNT(*) FROM ref_commissions c WHERE c.referred_id=r.referred_id) n, "
                       "(SELECT COALESCE(SUM(amount),0) FROM ref_commissions c WHERE c.referred_id=r.referred_id) earned "
                       "FROM referrals r LEFT JOIN users u ON u.id=r.referred_id WHERE r.referrer_id=? "
                       "ORDER BY r.created DESC LIMIT 15", (uid,))
    friends = [f"👤 <b>{esc(x['name'] or x['id'])}</b> · {x['n']} trx · {rp(x['earned'])}" for x in rows]
    more = f"\n<i>+ {st['friends'] - len(rows)} lainnya</i>" if st["friends"] > len(rows) else ""
    share = "https://t.me/share/url?url=" + urlquote(link) + "&text=" + urlquote("Beli nomor virtual OTP otomatis di sini 👇")
    await show_any(cb, ref_text(link, st, bal, friends, more),
                   kb([[b("💸 Tarik Saldo Referral", "refwd")],
                       [InlineKeyboardButton(text="📤 Bagikan Link", url=share)],
                       [b("🏠 Menu Utama", "home")]]))

@r.callback_query(F.data == "refwd")
async def ref_wd(cb: CallbackQuery, state: FSMContext):
    bal = await ref_bal(cb.from_user.id)
    if bal < REF_MIN_WD:
        return await cb.answer(f"Saldo referral kamu {rp(bal)}. Minimal penarikan {rp(REF_MIN_WD)}.", show_alert=True)
    await cb.answer()
    await state.set_state(Wd.form)
    await cb.message.answer(
        f"💸 <b>FORMULIR PENARIKAN SALDO REFERRAL</b> 💸\n\n"
        f"Saldo Anda saat ini: <b>{rp(bal)}</b>\n\n"
        f"Silakan balas pesan ini dengan format berikut untuk memproses penarikan:\n\n"
        f"<code>PILIHAN_METODE / NOMOR_E-WALLET / NAMA_PEMILIK_AKUN</code>\n\n"
        f"<b>Contoh Ke DANA:</b>\n<code>DANA / 081234567890 / Budi Santoso</code>\n\n"
        f"<b>Contoh Ke GoPay:</b>\n<code>GOPAY / 081234567890 / Budi Santoso</code>\n\n"
        f"<b>Contoh Ke Saldo Bot:</b>\n<code>SALDO BOT / [Ketik: MASUKKAN KE SALDO BOT]</code>\n\n"
        f"⚠️ Pastikan nomor dan nama e-wallet sudah benar. Kesalahan input bukan tanggung jawab admin!",
        reply_markup=kb([[b("❌ Batal", "ref")]]))

_wd_warned = False

def wd_chan_target():
    """Tentukan chat tujuan laporan WD. Bot hanya bisa kirim ke ID numerik atau @username, bukan link undangan privat."""
    v = WD_CHANNEL_ID
    if v:
        return int(v) if v.lstrip("-").isdigit() else (v if v.startswith("@") else "@" + v)
    u = WD_CHANNEL_URL
    if not u: return None
    m = re.search(r"t\.me/c/(\d+)", u)
    if m: return int("-100" + m.group(1))
    m = re.search(r"t\.me/([A-Za-z][A-Za-z0-9_]{3,})", u)
    if m and m.group(1).lower() not in ("joinchat", "c", "s"): return "@" + m.group(1)
    if u.startswith("@"): return u
    return None

WD_STATUS = {"PENDING": "⏳ Pending", "DONE": "✅ Berhasil (Disetujui)", "REJECTED": "❌ Ditolak"}

def wd_chan_text(w, status):
    wallet = "Saldo Bot" if w["method"] == "SALDO BOT" else f"{w['method']} · <code>{esc(mask_phone(w['account']))}</code>"
    return (f"💸 <b>PENARIKAN REFERRAL #{w['id']}</b>\n{LINE}\n"
            f"🆔 ID User: <code>{w['user_id']}</code>\n"
            f"💰 Total Penarikan: <b>{rp(w['amount'])}</b>\n"
            f"🏦 E-Wallet: {wallet}\n"
            f"✂️ Biaya: {rp(w['fee'])} · Diterima: <b>{rp(w['amount'] - w['fee'])}</b>\n"
            f"📌 Status: <b>{WD_STATUS.get(status, status)}</b>\n"
            f"🕒 {_tgl(w.get('created') or time.time())}")

async def wd_chan_post(bot: Bot, w, status="PENDING"):
    """Kirim laporan WD ke channel; kalau sudah pernah dikirim, edit pesan lama (update status)."""
    global _wd_warned
    t = wd_chan_target()
    if t is None:
        if (WD_CHANNEL_ID or WD_CHANNEL_URL) and not _wd_warned:
            _wd_warned = True
            for a in ADMINS:
                try:
                    await bot.send_message(a, "⚠️ Laporan WD ke channel belum bisa dikirim: link privat tidak bisa dipakai bot. "
                                              "Isi env <code>WD_CHANNEL_ID</code> dengan ID channel (contoh -1001234567890).")
                except Exception: pass
        return
    try:
        if w.get("chan_msg"):
            await bot.edit_message_text(wd_chan_text(w, status), chat_id=t, message_id=w["chan_msg"])
        else:
            sent = await bot.send_message(t, wd_chan_text(w, status))
            await run("UPDATE withdrawals SET chan_msg=? WHERE id=?", (sent.message_id, w["id"]))
    except TelegramBadRequest as e:
        if "not modified" not in str(e): log.warning("laporan WD ke channel gagal: %s", e)
    except Exception as e:
        log.warning("laporan WD ke channel gagal: %s", e)

def wd_admin_text(w, name):
    net = w["amount"] - w["fee"]
    t = (f"💸 <b>PERMINTAAN PENARIKAN #{w['id']}</b>\n{LINE}\n👤 {esc(name)} (<code>{w['user_id']}</code>)\n"
         f"🏦 Metode: <b>{esc(w['method'])}</b>\n")
    if w["method"] != "SALDO BOT":
        t += f"📱 Nomor: <code>{esc(w['account'])}</code>\n🧾 A/N: {esc(w['holder'])}\n"
    t += f"💰 Jumlah: {rp(w['amount'])}\n✂️ Biaya: {rp(w['fee'])}\n✅ <b>Dikirim: {rp(net)}</b>"
    return t

@r.message(Wd.form, F.text, ~F.text.startswith("/"))
async def ref_wd_submit(m: Message, state: FSMContext, bot: Bot):
    uid = m.from_user.id
    parts = [p.strip() for p in m.text.split("/")]
    method = " ".join(parts[0].upper().split())
    retry = kb([[b("❌ Batal", "ref")]])
    if method not in ("DANA", "GOPAY", "SALDO BOT"):
        return await m.answer("❌ Metode tidak dikenal. Pilih: <b>DANA</b>, <b>GOPAY</b>, atau <b>SALDO BOT</b>. Coba kirim ulang.", reply_markup=retry)
    acc = holder = ""
    if method != "SALDO BOT":
        acc = re.sub(r"[\s\-+]", "", parts[1]) if len(parts) > 1 else ""
        holder = parts[2] if len(parts) > 2 else ""
        if not (acc.isdigit() and 9 <= len(acc) <= 15 and holder):
            return await m.answer("❌ Format salah. Contoh:\n<code>DANA / 081234567890 / Budi Santoso</code>", reply_markup=retry)
    amount = await ref_bal(uid)
    if amount < REF_MIN_WD:
        await state.clear()
        return await m.answer(f"❌ Saldo referral {rp(amount)}, minimal penarikan {rp(REF_MIN_WD)}.")
    fee = REF_GOPAY_FEE if method == "GOPAY" else 0
    if await run("UPDATE users SET ref_balance=ref_balance-? WHERE id=? AND ref_balance>=?", (amount, uid, amount)) == 0:
        await state.clear()
        return await m.answer("❌ Saldo tidak mencukupi.")
    cur = await db.execute("INSERT INTO withdrawals(user_id,amount,method,account,holder,fee,created) VALUES(?,?,?,?,?,?,?)",
                           (uid, amount, method, acc, holder, fee, time.time()))
    await db.commit()
    await state.clear()
    w = {"id": cur.lastrowid, "user_id": uid, "amount": amount, "method": method, "account": acc, "holder": holder, "fee": fee,
         "created": time.time()}
    await wd_chan_post(bot, w, "PENDING")
    await m.answer(f"✅ <b>Permintaan penarikan #{w['id']} diterima</b>\n{LINE}\n<blockquote>🏦 {esc(method)}\n"
                   f"💰 {rp(amount)} (biaya {rp(fee)})\n⏳ Diproses admin dalam 1-24 jam.</blockquote>",
                   reply_markup=kb([[b("🎁 Menu Referral", "ref")], [b("🏠 Menu Utama", "home")]]))
    for a in ADMINS:
        try:
            await bot.send_message(a, wd_admin_text(w, m.from_user.full_name),
                                   reply_markup=kb([[b("✅ Setujui", f"wdok:{w['id']}"), b("❌ Tolak", f"wdno:{w['id']}")]]))
        except Exception:
            log.warning("gagal kirim permintaan WD ke admin %s", a)

@r.callback_query(F.data.startswith(("wdok:", "wdno:")))
async def wd_decide(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMINS:
        return await cb.answer("Khusus admin.", show_alert=True)
    act, wid = cb.data.split(":")
    w = await one("SELECT * FROM withdrawals WHERE id=?", (int(wid),))
    if not w:
        return await cb.answer("Data tidak ditemukan.", show_alert=True)
    ok = act == "wdok"
    if await run("UPDATE withdrawals SET status=? WHERE id=? AND status='PENDING'", ("DONE" if ok else "REJECTED", w["id"])) == 0:
        return await cb.answer("Sudah diproses sebelumnya.", show_alert=True)
    net = w["amount"] - w["fee"]
    if ok:
        if w["method"] == "SALDO BOT":
            await credit(w["user_id"], w["amount"])
        msg = (f"✅ <b>Penarikan #{w['id']} disetujui</b>\n<blockquote>"
               + (f"{rp(w['amount'])} sudah masuk ke saldo bot kamu." if w["method"] == "SALDO BOT"
                  else f"{rp(net)} dikirim ke {esc(w['method'])} {esc(w['account'])}.") + "</blockquote>")
    else:
        await run("UPDATE users SET ref_balance=COALESCE(ref_balance,0)+? WHERE id=?", (w["amount"], w["user_id"]))
        msg = f"❌ <b>Penarikan #{w['id']} ditolak</b>\n<blockquote>{rp(w['amount'])} dikembalikan ke saldo referral kamu. Hubungi admin jika ada pertanyaan.</blockquote>"
    try:
        await bot.send_message(w["user_id"], msg)
    except Exception:
        log.warning("gagal kabari user %s soal WD", w["user_id"])
    await wd_chan_post(bot, w, "DONE" if ok else "REJECTED")
    await cb.answer("Disetujui" if ok else "Ditolak")
    try:
        await cb.message.edit_text(cb.message.html_text + f"\n\n{'✅ DISETUJUI' if ok else '❌ DITOLAK'} oleh {esc(cb.from_user.full_name)}")
    except TelegramBadRequest:
        pass

@r.message(Command("wdlist"))
async def wdlist(m: Message):
    if m.from_user.id not in ADMINS: return
    rows = await fetch("SELECT w.*, u.name FROM withdrawals w LEFT JOIN users u ON u.id=w.user_id WHERE w.status='PENDING' ORDER BY w.id LIMIT 20")
    if not rows: return await m.answer("Tidak ada penarikan yang menunggu.")
    for w in rows:
        await m.answer(wd_admin_text(w, w["name"] or w["user_id"]),
                       reply_markup=kb([[b("✅ Setujui", f"wdok:{w['id']}"), b("❌ Tolak", f"wdno:{w['id']}")]]))

@r.message(Command("setref"))
async def setref(m: Message):
    """Admin: /setref <id_pengajak> <id_user1> [id_user2 ...] - hubungkan teman lama secara manual (komisi berlaku untuk transaksi berikutnya)."""
    if m.from_user.id not in ADMINS: return
    a = m.text.split()[1:]
    if len(a) < 2 or not all(x.isdigit() for x in a):
        return await m.answer("Format: /setref id_pengajak id_user1 [id_user2 ...]")
    ref, ids = int(a[0]), [int(x) for x in a[1:]]
    if not await one("SELECT 1 x FROM users WHERE id=?", (ref,)):
        return await m.answer("❌ ID pengajak tidak ada di database.")
    ok, skip = 0, []
    for uid in ids:
        if uid == ref or not await one("SELECT 1 x FROM users WHERE id=?", (uid,)) \
                or await one("SELECT 1 x FROM referrals WHERE referred_id=?", (uid,)):
            skip.append(uid); continue
        await run("INSERT INTO referrals(referred_id,referrer_id,created) VALUES(?,?,?)", (uid, ref, time.time()))
        ok += 1
    await m.answer(f"✅ Tercatat: {ok}" + (f"\n⚠️ Dilewati (tidak ada di DB / sudah punya pengajak / diri sendiri): {', '.join(map(str, skip))}" if skip else ""))

@r.message(Command("refstats"))
async def refstats(m: Message):
    if m.from_user.id not in ADMINS: return
    rows = await fetch("SELECT r.referrer_id id, u.name, COUNT(*) n, COALESCE(u.ref_balance,0) bal, "
                       "(SELECT COALESCE(SUM(amount),0) FROM ref_commissions c WHERE c.referrer_id=r.referrer_id) earned "
                       "FROM referrals r LEFT JOIN users u ON u.id=r.referrer_id GROUP BY r.referrer_id ORDER BY earned DESC, n DESC LIMIT 15")
    if not rows: return await m.answer("Belum ada data referral.")
    lines = [f"• <b>{esc(x['name'] or x['id'])}</b> (<code>{x['id']}</code>) · teman {x['n']} · komisi {rp(x['earned'])} · saldo {rp(x['bal'])}" for x in rows]
    await m.answer(f"🎁 <b>STATISTIK REFERRAL</b>\n{LINE}\n" + "\n".join(lines))


# ---------- beli nomor: LAYANAN -> NEGARA -> DAFTAR NOMOR (+ operator opsional) ----------
def svc_rank(s):
    n = s["name"].lower()
    return (next((i for i, p in enumerate(PRIORITY) if p in n), 99), n)

@r.callback_query(F.data.startswith("sv:"))
async def services(cb: CallbackQuery):
    await cb.answer()
    data = sorted([s for s in await cached("/catalog/services", ttl=600) if s.get("active")], key=svc_rank)
    rows = pager(data, int(cb.data.split(":")[1]), lambda s: b(f"📲 {s['name']}", f"co:{s['id']}:0"), "sv")
    rows.append([b("🏠 Menu Utama", "home")])
    await show(cb, f"📲 <b>PILIH LAYANAN</b>\n{LINE}\n<i>Pilih aplikasi yang ingin diverifikasi</i>", kb(rows))

@r.callback_query(F.data.startswith("co:"))
async def countries(cb: CallbackQuery):
    _, sid, page = cb.data.split(":")
    await cb.answer()
    stats, sr = await country_stats(sid), await sr_stats(sid)
    cs = [c for c in await cached("/catalog/countries", ttl=600) if c.get("active")]
    code = lambda c: str(c.get("code", "")).upper()
    prio = [c for pc in PRIO_COUNTRIES for c in cs if code(c) == pc]
    rest = sorted([c for c in cs if code(c) not in PRIO_COUNTRIES and c["id"] in stats],
                  key=lambda c: (stats[c["id"]]["price"], c["name"]))
    def mk(c):
        flag, st = c.get("emoji", ""), stats.get(c["id"])
        if not st:
            return b(f"🔴 {flag} {c['name']} - Stok habis", "ne")
        s = sr.get(c["id"])
        emo = "🟢" if s is None or s >= 50 else "🟡" if s >= 20 else "🔴"
        srt = "SR baru" if s is None else f"SR {s}%" + (" 🔥" if s >= 60 else "")
        return b(f"{emo} {flag} {c['name']} - {srt} - {rp(sell_price(st['price'], c))}", f"of:{sid}:{c['id']}:0:0")
    rows = pager(prio + rest, int(page), mk, f"co:{sid}")
    rows.append([b("‹ Layanan", "sv:0"), b("🏠 Menu Utama", "home")])
    await show(cb, f"🌍 <b>PILIH NEGARA</b>\n{LINE}\n<blockquote>📲 {esc(await svc_name(sid))}</blockquote>\n"
                   f"<i>SR = persentase OTP masuk dari transaksi toko (14 hari terakhir).\n🟢 bagus · 🟡 sedang · 🔴 rendah/habis</i>", kb(rows))

@r.callback_query(F.data == "ne")
async def no_stock(cb: CallbackQuery):
    await cb.answer("Stok negara ini sedang kosong.", show_alert=True)

async def offer_list_content(sid, cid, oid, page):
    c, svc, items = await country_of(cid), await svc_name(sid), await offers(sid, cid, oid)
    back = [b("‹ Negara", f"co:{sid}:0"), b("🏠 Menu Utama", "home")]
    op_row = [b("📡 Pilih Operator (Opsional)", f"op:{sid}:{cid}:0")]
    head = (f"📞 <b>DAFTAR NOMOR</b>\n{LINE}\n<blockquote>🏢 {esc(svc)}\n🌍 {c.get('emoji', '')} {esc(c.get('name', ''))}\n"
            f"📡 Operator: {esc(await op_name(sid, cid, oid))}</blockquote>\n")
    if not items:
        return head + "😕 <i>Stok kosong untuk pilihan ini.</i>", kb([op_row, back])
    pages = max(1, math.ceil(len(items) / PER_PAGE))
    def make_offer(p):
        price = sell_price(p["price"], c)
        return b(f"📞 {rp(price)} · {p.get('operator_name') or 'Any'} · stok {p['available']}",
                 f"cf:{sid}:{cid}:{oid}:{p['id']}:{price}")
    rows = pager(items, int(page), make_offer, f"of:{sid}:{cid}:{oid}")
    rows += [op_row, back]
    text = head + f"<i>Termurah dulu · Hal {min(int(page), pages - 1) + 1}/{pages}</i>"
    return text, kb(rows)

@r.callback_query(F.data.startswith("of:"))
async def offer_list(cb: CallbackQuery):
    _, sid, cid, oid, page = cb.data.split(":")
    await cb.answer()
    text, markup = await offer_list_content(sid, cid, oid, page)
    await show(cb, text, markup)

@r.callback_query(F.data.startswith("op:"))
async def operators(cb: CallbackQuery):
    _, sid, cid, page = cb.data.split(":")
    ops = await cached("/catalog/operators", {"country_id": cid, "platform_id": sid}, ttl=120)
    if not ops:
        return await cb.answer("Tidak ada pilihan operator untuk negara ini.", show_alert=True)
    await cb.answer()
    def mk(o):
        oid = o.get("operator_id") or 0
        return b("🌐 Semua Operator (Any)" if not oid else f"📡 {o.get('name') or o.get('local_name')}", f"of:{sid}:{cid}:{oid}:0")
    rows = pager(ops, int(page), mk, f"op:{sid}:{cid}")
    rows.append([b("‹ Daftar Nomor", f"of:{sid}:{cid}:0:0"), b("🏠 Menu Utama", "home")])
    await show(cb, f"📡 <b>PILIH OPERATOR</b>\n{LINE}\n<i>Opsional — saring nomor berdasarkan operator</i>", kb(rows))

async def confirm_view(cb, sid, cid, oid, pid):
    available = await offers(sid, cid, oid)
    p = (available[0] if available else None) if pid is None else \
        next((x for x in available if str(x["id"]) == str(pid)), None)
    back = [b("‹ Daftar Nomor", f"of:{sid}:{cid}:{oid}:0")]
    if not p:
        return await show(cb, "😕 Nomor ini sudah tidak tersedia. Pilih penawaran lain.", kb([back]))
    c, svc = await country_of(cid), await svc_name(sid)
    price = sell_price(p["price"], c)
    bal = await balance(cb.from_user.id, cb.from_user.full_name)
    await show(cb, f"🛍 <b>KONFIRMASI PESANAN</b>\n{LINE}\n<blockquote>🏢 Layanan: {esc(svc)} ({esc(c.get('name', ''))})\n"
                   f"📡 Operator: {esc(p.get('operator_name') or 'Any')}\n📦 Stok: <b>{p['available']}</b>\n"
                   f"💰 Tarif: <b>{rp(price)}</b></blockquote>\n💵 Saldo Anda: <b>{rp(bal)}</b>\n\n"
                   f"♻️ <i>OTP tidak masuk = saldo kembali otomatis</i>",
               kb([[b(f"🛒 Beli Sekarang · {rp(price)}", f"by:{sid}:{cid}:{oid}:{p['id']}:{price}")], back]))

async def acknowledge_callback(cb: CallbackQuery, bot: Bot, prompt):
    """Jawab callback sebelum ada panggilan API yang bisa memakan waktu."""
    try:
        await cb.answer(prompt)
        return True
    except TelegramBadRequest as e:
        error = str(e).lower()
        if "query is too old" not in error and "query id is invalid" not in error:
            raise
        log.info("Callback sudah kedaluwarsa: %s", e)
        try:
            await bot.send_message(cb.message.chat.id,
                                   "⌛ Tombol sudah kedaluwarsa. Silakan tekan lagi penawaran di daftar nomor.")
        except Exception:
            log.exception("gagal memberi tahu pengguna tentang tombol kedaluwarsa")
        return False


async def place_order(cb: CallbackQuery, bot: Bot, sid, cid, oid, pid, shown=None):
    """Beli penawaran tanpa mengubah pesan sumber, lalu kirim kartu pesanan baru."""
    if not await acknowledge_callback(cb, bot, "Memproses pembelian…"):
        return
    uid = cb.from_user.id
    c, svc = await country_of(cid), await svc_name(sid)
    available_offers = await offers(sid, cid, oid)
    p = (available_offers[0] if available_offers else None) if pid is None else next((x for x in available_offers if str(x["id"]) == str(pid)), None)
    if not p:
        await bot.send_message(cb.message.chat.id, "😕 Stok habis. Daftar nomor di atas tetap tersedia.")
        return
    price = sell_price(p["price"], c)
    if shown is not None and price > int(shown):
        await bot.send_message(cb.message.chat.id,
                               "💰 Harga berubah. Pilih ulang dari daftar nomor agar tidak membayar lebih.")
        return
    if not await deduct(uid, price):
        await bot.send_message(cb.message.chat.id, "💳 Saldo tidak cukup. Silakan top up dulu.",
                               reply_markup=kb([[b("💳 Top Up Saldo", "dep")]]))
        return
    d, err = await api("POST", "/orders/create", headers={"Idempotency-Key": uuid.uuid4().hex},
                       json={"product_id": p["id"], "quantity": 1})
    if err or not d or not d.get("orders"):
        await credit(uid, price)
        if err == "INSUFFICIENT_BALANCE":
            for a in ADMINS:
                await bot.send_message(a, "⚠️ Saldo SMSCode habis! Segera top up.")
        msg = "Stok habis, coba lagi nanti." if err == "NO_OFFER_AVAILABLE" else \
              "Layanan sedang sibuk, saldo Anda aman. Coba lagi sebentar."
        try:
            await bot.send_message(cb.message.chat.id, f"😕 {msg}",
                                   reply_markup=kb([[b("‹ Segarkan Daftar Nomor", f"of:{sid}:{cid}:{oid}:0")]]))
        except Exception:
            log.exception("gagal mengirim pesan kegagalan pembelian")
        return

    o_ = d["orders"][0]
    label = f"{svc} · {c.get('emoji', '')} {c.get('name', '')}".strip()
    order = {"id": o_["id"], "phone": o_["phone_number"], "price": price, "status": "ACTIVE",
             "label": label, "svc": svc, "ctry": c.get("name", ""), "otp": None, "code": None,
             "msg": None, "rev": 0, "sid": int(sid), "cid": int(cid), "oid": int(oid)}

    sent, is_photo = None, 0
    try:
        sent = await bot.send_message(cb.message.chat.id, card(order), reply_markup=card_kb(order))
    except Exception:
        log.exception("kirim kartu nomor sebagai teks gagal")

    msg_id = sent.message_id if sent else 0
    await db.execute("INSERT INTO orders(id,user_id,label,phone,price,status,chat_id,msg_id,created,sid,cid,oid,svc,ctry,ph)"
                     " VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                     (o_["id"], uid, label, o_["phone_number"], price, "ACTIVE", cb.message.chat.id, msg_id,
                      time.time(), int(sid), int(cid), int(oid), svc, c.get("name", ""), is_photo))
    await db.commit()


@r.callback_query(F.data.startswith("cf:"))
async def confirm(cb: CallbackQuery, bot: Bot):
    parts = cb.data.split(":")
    _, sid, cid, oid, pid, *shown = parts
    await place_order(cb, bot, sid, cid, oid, pid, shown[0] if shown else None)

async def own_order(cb, oid):
    o = await one("SELECT * FROM orders WHERE id=? AND user_id=?", (int(oid), cb.from_user.id))
    if not o:
        await cb.answer("Pesanan tidak ditemukan.", show_alert=True)
    return o

@r.callback_query(F.data.startswith("rb:"))
async def rebuy(cb: CallbackQuery, bot: Bot):
    """Buat pesanan baru tanpa mengubah kartu pesanan yang menampilkan tombol ini."""
    o = await own_order(cb, cb.data.split(":")[1])
    if not o:
        return
    if not o.get("sid") or not o.get("cid"):
        return await cb.answer("Pilihan nomor untuk pesanan ini tidak tersedia.", show_alert=True)
    await place_order(cb, bot, str(o["sid"]), str(o["cid"]), str(o.get("oid") or 0),
                      None, o["price"])

@r.callback_query(F.data.startswith("by:"))
async def buy(cb: CallbackQuery, bot: Bot):
    _, sid, cid, oid, pid, shown = cb.data.split(":")
    await place_order(cb, bot, sid, cid, oid, pid, shown)

@r.callback_query(F.data.startswith(("en:", "cx:", "fin:")))
async def end_order(cb: CallbackQuery):
    """Selesai (jika OTP sudah masuk) atau Batal + refund (jika belum)."""
    o = await own_order(cb, cb.data.split(":")[1])
    if not o: return
    if o["status"] not in ("ACTIVE", "OTP"):
        return await cb.answer("Pesanan ini sudah selesai.", show_alert=True)
    if o["otp"]:
        await api("POST", "/orders/finish", json={"id": o["id"]})
        await run("UPDATE orders SET status='COMPLETED' WHERE id=? AND refunded=0", (o["id"],))
    else:
        d, err = await api("POST", "/orders/cancel", json={"id": o["id"]})
        if err == "CANCEL_TOO_EARLY":
            return await cb.answer("Tunggu minimal 2 menit sebelum membatalkan.", show_alert=True)
        if err:
            return await cb.answer("Gagal membatalkan, coba lagi.", show_alert=True)
        await refund(o["id"], "CANCELED")
    await cb.answer()
    o = await one("SELECT * FROM orders WHERE id=?", (o["id"],))
    await show(cb, card(o), card_kb(o))

@r.callback_query(F.data.startswith("rs:"))
async def resend(cb: CallbackQuery):
    o = await own_order(cb, cb.data.split(":")[1])
    if not o: return
    d, err = await api("POST", "/orders/resend", json={"id": o["id"]})
    await cb.answer("📨 Permintaan SMS baru dikirim." if d and d.get("resent") else "Layanan ini tidak mendukung kirim ulang.", show_alert=True)

@r.callback_query(F.data.startswith("cp:"))
async def copy_fallback(cb: CallbackQuery):
    _, oid, kind = cb.data.split(":")
    o = await own_order(cb, oid)
    if o:
        await cb.answer(o["phone"] if kind == "n" else (o.get("code") or o.get("otp") or "-"), show_alert=True)

@r.callback_query(F.data.regexp(r"^(c|s|p|q|ok):"))
async def old_menu(cb: CallbackQuery):
    await cb.answer("Menu sudah diperbarui. Ketik /start untuk membuka menu terbaru.", show_alert=True)


# ---------- deposit ----------
class Dep(StatesGroup):
    amount = State()

@r.callback_query(F.data == "dep")
async def dep(cb: CallbackQuery):
    await cb.answer()
    amts = [10000, 20000, 50000, 100000]
    rows = [[b("💳 " + rp(a), f"dp:{a}") for a in amts[:2]], [b("💳 " + rp(a), f"dp:{a}") for a in amts[2:]],
            [b("✏️ Nominal Lain", "dpx")], [b("🏠 Menu Utama", "home")]]
    await show(cb, f"💳 <b>TOP UP SALDO</b>\n{LINE}\n<i>Pilih nominal (min. {rp(MIN_DEP)})</i>", kb(rows))

@r.callback_query(F.data == "dpx")
async def dpx(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    await state.set_state(Dep.amount)
    await show(cb, f"✏️ Ketik nominal deposit (angka saja, min. {rp(MIN_DEP)}):")

@r.message(Dep.amount)
async def dep_amount(m: Message, state: FSMContext):
    txt = (m.text or "").replace(".", "").replace(",", "").strip()
    if not txt.isdigit() or int(txt) < MIN_DEP:
        return await m.answer(f"Nominal tidak valid. Minimal {rp(MIN_DEP)}.")
    await state.clear()
    await ask_deposit(m, m.from_user.id, int(txt))

async def send_invoice(target, uid, amount):
    if KASERA_KEY:
        return await kasera_invoice(target, uid, amount)
    code = random.randint(1, 999)  # kode unik agar mudah dicocokkan admin
    total = amount + code
    cur = await db.execute("INSERT INTO deposits(user_id,amount,total,created) VALUES(?,?,?,?)", (uid, amount, total, time.time()))
    await db.commit()
    text = (f"🧾 <b>Invoice Deposit #{cur.lastrowid}</b>\n{LINE}\n💸 Transfer tepat: <b>{rp(total)}</b>\n"
            f"✅ Saldo masuk: <b>{rp(amount)}</b>\n\n{esc(PAY_INFO)}\n\nSetelah transfer, tekan tombol di bawah.")
    markup = kb([[b("✅ Saya sudah bayar", f"paid:{cur.lastrowid}")]])
    msg = target.message if isinstance(target, CallbackQuery) else target
    if os.path.exists("qris.jpg"):
        await msg.answer_photo(FSInputFile("qris.jpg"), caption=text, reply_markup=markup)
    else:
        await msg.answer(text, reply_markup=markup)

@r.callback_query(F.data.startswith("dp:"))
async def dp(cb: CallbackQuery):
    await cb.answer()
    await ask_deposit(cb, cb.from_user.id, int(cb.data.split(":")[1]))

async def ask_deposit(target, uid, amount):
    """Tampilkan rincian top up (biaya admin Kasera ditanggung pembeli) lalu minta konfirmasi."""
    msg = target.message if isinstance(target, CallbackQuery) else target
    if amount < MIN_DEP:
        return await msg.answer(f"⚠️ Minimal top up adalah {rp(MIN_DEP)}.")
    if not KASERA_KEY:  # mode manual: tanpa biaya admin Kasera
        return await send_invoice(target, uid, amount)
    q = hitung_tagihan_kasera(amount, "QRIS")
    await msg.answer(
        f"📝 <b>KONFIRMASI TOP UP SALDO</b>\n{LINE}\n"
        f"<blockquote>💰 Saldo masuk  <b>{rp(q['nominal_saldo'])}</b>\n"
        f"🧾 Biaya admin  <b>{rp(q['biaya_admin'])}</b>\n📲 Metode  <b>QRIS</b></blockquote>\n"
        f"💳 <b>Total bayar: {rp(q['total_bayar'])}</b>\n\n"
        f"<i>Biaya admin ditanggung pembeli, saldo yang masuk utuh {rp(q['nominal_saldo'])}.</i>",
        reply_markup=kb([[b(f"✅ Bayar {rp(q['total_bayar'])}", f"dpc:{amount}")],
                         [b("‹ Ganti Nominal", "dep"), b("🏠 Menu", "hm")]]))

@r.callback_query(F.data.startswith("dpc:"))
async def dp_confirm(cb: CallbackQuery):
    await cb.answer()
    amount = int(cb.data.split(":")[1])
    if amount < MIN_DEP:
        return
    try:  # hapus tombol agar tidak terbuat dua invoice karena klik ganda
        await cb.message.edit_reply_markup(reply_markup=None)
    except TelegramBadRequest:
        pass
    await send_invoice(cb, cb.from_user.id, amount)

@r.callback_query(F.data.startswith("paid:"))
async def paid(cb: CallbackQuery, bot: Bot):
    d = await one("SELECT * FROM deposits WHERE id=? AND user_id=? AND status='PENDING'", (int(cb.data.split(":")[1]), cb.from_user.id))
    if not d:
        return await cb.answer("Invoice tidak ditemukan.", show_alert=True)
    await cb.message.edit_reply_markup(reply_markup=None)
    await cb.answer("Menunggu verifikasi admin ⏳", show_alert=True)
    for a in ADMINS:
        await bot.send_message(a, f"💰 <b>Deposit #{d['id']}</b>\nUser: {esc(cb.from_user.full_name)} (<code>{d['user_id']}</code>)\n"
                                  f"Transfer: <b>{rp(d['total'])}</b>\nSaldo: <b>{rp(d['amount'])}</b>",
                               reply_markup=kb([[b("✅ Terima", f"dpa:{d['id']}"), b("❌ Tolak", f"dpr:{d['id']}")]]))

@r.callback_query(F.data.startswith(("dpa:", "dpr:")))
async def dep_decide(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMINS:
        return await cb.answer("Khusus admin.", show_alert=True)
    act, did = cb.data.split(":")
    ok = act == "dpa"
    if await run("UPDATE deposits SET status=? WHERE id=? AND status='PENDING'", ("OK" if ok else "REJECTED", int(did))) == 0:
        return await cb.answer("Sudah diproses.", show_alert=True)
    d = await one("SELECT * FROM deposits WHERE id=?", (int(did),))
    if ok:
        await credit(d["user_id"], d["amount"])
        await bot.send_message(d["user_id"], f"✅ Deposit <b>{rp(d['amount'])}</b> berhasil! Selamat berbelanja 🎉")
    else:
        await bot.send_message(d["user_id"], f"❌ Deposit #{d['id']} ditolak. Hubungi admin jika ada kesalahan.")
    await cb.message.edit_text(cb.message.html_text + f"\n\n{'✅ Diterima' if ok else '❌ Ditolak'}")


# ---------- Kasera Pay (QRIS otomatis) ----------
async def kasera(method, path, headers=None, **kw):
    try:
        async with http.request(method, "https://pay.kasera.id" + path, timeout=aiohttp.ClientTimeout(total=20),
                                headers={"Authorization": f"Bearer {KASERA_KEY}", **(headers or {})}, **kw) as resp:
            status = resp.status
            try:
                j = await resp.json()
            except Exception:
                j = {"raw": (await resp.text())[:500]}
    except Exception as e:
        log.warning("Kasera %s %s gagal (exception): %s", method, path, e)
        return None, f"network: {e}"
    if status < 300:
        return j, None
    detail = j.get("error", {}) if isinstance(j, dict) else {}
    code = detail.get("code") or detail.get("message") or j.get("raw") or f"HTTP {status}"
    log.warning("Kasera %s %s gagal (HTTP %s): %s", method, path, status, j)
    return None, str(code)

def qr_png(data):
    buf = io.BytesIO()
    qrcode.make(data).save(buf, format="PNG")
    return buf.getvalue()

FEE_RULES = {"QRIS": (FEE_PCT_BPS, FEE_FIXED), "VA": (0, 5000)}   # (persen dalam basis poin, biaya tetap Rp)

def _ceil_div(a, b): return -(-a // b)

def hitung_tagihan_kasera(nominal_bersih: int, metode: str = "QRIS") -> dict:
    """Gross-up: total yang dibayar pembeli agar saldo bersih yang masuk pas sesuai nominal.
    Pakai aritmetika bilangan bulat (tanpa float) supaya tidak ada selisih pembulatan."""
    bps, fixed = FEE_RULES.get(metode.upper(), (0, 0))
    nominal = int(nominal_bersih)
    total = _ceil_div((nominal + fixed) * 10000, 10000 - bps)
    fee_kasera = _ceil_div(total * bps, 10000) + fixed       # biaya yang dipotong Kasera dari total
    return {"nominal_saldo": nominal, "total_bayar": total, "biaya_admin": total - nominal,
            "fee_kasera": fee_kasera, "diterima_kamu": total - fee_kasera}

async def kasera_invoice(target, uid, amount):
    msg = target.message if isinstance(target, CallbackQuery) else target
    q = hitung_tagihan_kasera(amount, "QRIS")
    total = q["total_bayar"]
    cur = await db.execute("INSERT INTO deposits(user_id,amount,total,created) VALUES(?,?,?,?)", (uid, amount, total, time.time()))
    await db.commit()
    did = cur.lastrowid
    tx, err = await kasera("POST", "/v1/transactions", headers={"Idempotency-Key": f"dep{did}"},
                           json={"amount": total, "payment_methods": ["qris"], "external_id": f"dep{did}",
                                 "description": f"Deposit #{did}", "expires_in_minutes": 30})
    if err:
        await run("UPDATE deposits SET status='FAILED' WHERE id=?", (did,))
        log.warning("Gagal membuat invoice Kasera untuk deposit #%s: %s", did, err)
        for a in ADMINS:
            try:
                await msg.bot.send_message(a, f"⚠️ Gagal membuat invoice Kasera (deposit #{did}):\n<code>{esc(err)}</code>")
            except Exception:
                pass
        return await msg.answer("😕 Gagal membuat invoice, coba lagi sebentar lagi.")
    await run("UPDATE deposits SET kasera_id=? WHERE id=?", (tx["id"], did))
    text = (f"🧾 <b>INVOICE TOP UP #{did}</b>\n{LINE}\n"
            f"<blockquote>💰 Saldo masuk  <b>{rp(amount)}</b>\n🧾 Biaya admin  <b>{rp(q['biaya_admin'])}</b>\n"
            f"💳 Total bayar  <b>{rp(total)}</b>\n📲 Metode  <b>QRIS</b>\n⏱ Berlaku  <b>30 menit</b></blockquote>\n"
            f"Scan QR di atas, saldo masuk <b>otomatis</b> setelah bayar ✅")
    markup = kb([[InlineKeyboardButton(text="🌐 Buka Halaman Bayar", url=tx["checkout_url"])], [b("🏠 Menu", "hm")]])
    qr = (tx.get("payment") or {}).get("qr_string")
    if qr:
        await msg.answer_photo(BufferedInputFile(qr_png(qr), "qris.png"), caption=text, reply_markup=markup)
    else:
        await msg.answer(text.replace("Scan QR di atas", "Buka halaman bayar di bawah"), reply_markup=markup)

async def settle(bot: Bot, did, paid_amount=None):
    """Tambahkan saldo untuk deposit yang lunas, tepat satu kali."""
    d = await one("SELECT * FROM deposits WHERE id=?", (did,))
    if not d or (paid_amount is not None and int(paid_amount) not in (d["total"], d["amount"])):
        log.warning("Deposit %s tidak cocok / tidak ditemukan", did)
        return False
    if await run("UPDATE deposits SET status='OK' WHERE id=? AND status IN ('PENDING','EXPIRED')", (did,)) == 0:
        return False
    await credit(d["user_id"], d["amount"])
    try:
        await bot.send_message(d["user_id"], f"✅ Deposit <b>{rp(d['amount'])}</b> berhasil! Saldo sudah masuk 🎉",
                               reply_markup=kb([[b("🛒 Beli Nomor", "sv:0")]]))
    except Exception:
        pass
    return True

async def kasera_webhook(request: web.Request):
    body = await request.read()
    t, v1s = None, []
    for part in request.headers.get("Kasera-Signature-V1", "").split(","):
        k, _, v = part.strip().partition("=")
        if k == "t": t = v
        elif k == "v1": v1s.append(v)
    if not (t and t.isdigit()) or abs(time.time() - int(t)) > 300:
        return web.Response(status=400, text="bad timestamp")
    expected = hmac.new(WH_SECRET.encode(), f"{t}.".encode() + body, hashlib.sha256).hexdigest()
    if not any(hmac.compare_digest(expected, v) for v in v1s):
        return web.Response(status=401, text="bad signature")
    ev = json.loads(body)
    if ev.get("type") == "payment.paid" and bool(ev.get("livemode")) == LIVE:
        data = ev["data"]
        ext = data.get("external_id", "")
        if ext.startswith("dep") and ext[3:].isdigit():
            await settle(request.app["bot"], int(ext[3:]), data.get("amount"))
    return web.Response(text="ok")  # selalu 2xx agar tidak dikirim ulang

_last_dep_check = 0.0
async def poll_deposits(bot: Bot):
    """Cadangan jika webhook terlewat: cek invoice pending tiap 30 detik."""
    global _last_dep_check
    if not KASERA_KEY or time.time() - _last_dep_check < 30: return
    _last_dep_check = time.time()
    for d in await fetch("SELECT * FROM deposits WHERE status='PENDING' AND kasera_id IS NOT NULL AND created>?", (time.time() - 7200,)):
        tx, _ = await kasera("GET", f"/v1/transactions/{d['kasera_id']}")
        if not tx: continue
        if tx["status"] == "succeeded":
            await settle(bot, d["id"], tx["amount"])
        elif tx["status"] in ("failed", "expired", "canceled"):
            await run("UPDATE deposits SET status='EXPIRED' WHERE id=? AND status='PENDING'", (d["id"],))
        await asyncio.sleep(1.1)


# ---------- admin ----------
@r.message(Command("admin"))
async def admin(m: Message):
    if m.from_user.id not in ADMINS: return
    d, _ = await api("GET", "/balance")
    u = (await one("SELECT COUNT(*) c FROM users"))["c"]
    o = await one("SELECT COUNT(*) c, COALESCE(SUM(price),0) s FROM orders WHERE refunded=0")
    await m.answer(f"🛠 <b>Admin</b>\n{LINE}\n👥 User: {u}\n🧾 Order sukses/aktif: {o['c']}\n💵 Omzet: {rp(o['s'])}\n"
                   f"🏦 Saldo SMSCode: {rp(d['balance']) if d else 'n/a'}\n\n"
                   f"/addsaldo &lt;user_id&gt; &lt;nominal&gt;\n/wdlist (penarikan referral menunggu)\n/setref &lt;id_pengajak&gt; &lt;id_user...&gt;\n/refstats\n/broadcast &lt;pesan&gt; (manual ke user)\n/trafik (laporan trafik, HANYA ke channel)\n/autobroadcast (promosi harga termurah, HANYA ke user)\n/testchannel\n/backup (kirim file database ke chat ini)\n/restore (kirim file .db dengan caption /restore)")

@r.message(Command("addsaldo"))
async def addsaldo(m: Message):
    if m.from_user.id not in ADMINS: return
    try:
        _, uid, amt = m.text.split()
        await balance(int(uid)); await credit(int(uid), int(amt))
        await m.answer(f"✅ Saldo {uid} +{rp(amt)}")
    except Exception:
        await m.answer("Format: /addsaldo user_id nominal")

@r.message(Command("broadcast"))
async def broadcast(m: Message, bot: Bot):
    if m.from_user.id not in ADMINS: return
    text = m.text.partition(" ")[2]
    if not text: return await m.answer("Format: /broadcast pesan")
    sent = 0
    for u in await fetch("SELECT id FROM users"):
        try:
            await bot.send_message(u["id"], text); sent += 1
        except Exception:
            pass
        await asyncio.sleep(0.05)
    await m.answer(f"📢 Terkirim ke {sent} user.")


# ---------- monitoring channel ----------
WIB = timezone(timedelta(hours=7))
_chan_warned = False

def mask_phone(phone):
    d = "".join(ch for ch in str(phone) if ch.isdigit())
    if len(d) < 7: return d
    return f"{d[:5 if len(d) >= 10 else 3]}•••{d[-3:]}"

def channel_text(o):
    t = (f"📡 <b>OTP TERKIRIM</b>\n🛠️ Layanan: {esc(o.get('svc') or o['label'])}\n🌍 Negara: {esc(o.get('ctry') or '-')}\n"
         f"📞 Nomor: <code>{mask_phone(o['phone'])}</code>\n🔑 Kode: <code>{esc(o.get('code') or '-')}</code>\n")
    if o.get("msg"): t += f"💬 \"{esc(str(o['msg'])[:300])}\"\n"
    return t + f"🕒 {datetime.now(WIB):%d/%m/%Y %H:%M:%S} WIB • #{o['id']}"

async def check_channel(bot):
    """None = siap/nonaktif, selain itu teks masalahnya."""
    if not CHANNEL_ID: return None
    try:
        me = await bot.get_me()
        m = await bot.get_chat_member(CHANNEL_ID, me.id)
        if m.status not in ("administrator", "creator"):
            return "Bot belum dijadikan admin di channel."
        if m.status == "administrator" and getattr(m, "can_post_messages", True) is False:
            return "Bot admin, tapi izin 'Post Messages' belum aktif."
    except Exception as e:
        return f"Tidak bisa mengakses channel (cek CHANNEL_ID & bot sudah ditambahkan): {e}"
    return None

async def monitor(bot, o):
    """Laporan otomatis ke channel setiap SMS/OTP masuk."""
    global _chan_warned
    if not CHANNEL_ID: return
    try:
        await bot.send_message(CHANNEL_ID, channel_text(o))
    except Exception as e:
        log.warning("Monitoring channel gagal: %s", e)
        if not _chan_warned:
            _chan_warned = True
            for a in ADMINS:
                try:
                    await bot.send_message(a, f"⚠️ Monitoring channel gagal: {esc(e)}\nPastikan bot admin channel (izin Post Messages). Tes dengan /testchannel")
                except Exception:
                    pass

@r.message(Command("testchannel"))
async def testchannel(m: Message, bot: Bot):
    if m.from_user.id not in ADMINS: return
    if not CHANNEL_ID:
        return await m.answer("❌ CHANNEL_ID belum diisi di Secrets.")
    err = await check_channel(bot)
    if not err:
        try:
            await bot.send_message(CHANNEL_ID, channel_text({"id": 0, "label": "Tes", "svc": "Tes Monitoring", "ctry": "Indonesia",
                                                             "phone": "+6281234567890", "code": "123456", "msg": "Ini pesan percobaan."}))
        except Exception as e:
            err = str(e)
    await m.answer("✅ Monitoring channel berfungsi. Cek channel Anda." if not err else f"❌ {esc(err)}")


# ---------- pemantau OTP ----------
async def poll(bot: Bot):
    rows = await fetch("SELECT * FROM orders WHERE status IN ('ACTIVE','OTP')")
    if not rows: return
    act, _ = await api("GET", "/orders/active")
    if act is None: return
    live = {a["id"]: a for a in act}
    for o in rows:
        a = live.get(o["id"])
        if a:
            code, text_, rev = a.get("otp_code"), a.get("otp_message"), a.get("sms_revision", 0)
            val = code or text_
            if val and rev > o["rev"]:
                await run("UPDATE orders SET status='OTP',otp=?,code=?,msg=?,rev=? WHERE id=?", (val, code, text_, rev, o["id"]))
                o = await one("SELECT * FROM orders WHERE id=?", (o["id"],))
                await refresh_card(bot, o)
                try:
                    await bot.send_message(o["user_id"], f"🔔 <b>OTP MASUK!</b> Pesanan #{o['id']}\n" + sms_text(o))
                except Exception:
                    log.warning("gagal kirim OTP ke user %s", o["user_id"])
                await monitor(bot, o)
                try:
                    await ref_commission(bot, o)
                except Exception:
                    log.exception("komisi referral gagal")
            elif o["status"] == "ACTIVE" and time.time() - o["created"] > AUTO_CANCEL:
                _, err = await api("POST", "/orders/cancel", json={"id": o["id"]})
                if not err and (done := await refund(o["id"], "CANCELED")):
                    await refresh_card(bot, await one("SELECT * FROM orders WHERE id=?", (o["id"],)))
                    await bot.send_message(o["user_id"], cancel_notice(o, done["price"], "OTP TIDAK MASUK",
                                           f"Kode tidak masuk dalam {AUTO_CANCEL // 60} menit, pesanan dibatalkan otomatis."),
                                           reply_markup=cancel_kb(o))
        else:
            d, _ = await api("GET", f"/orders/{o['id']}")
            if not d: continue
            if d["status"] in ("EXPIRED", "CANCELED") and not o["otp"]:
                if done := await refund(o["id"], d["status"]):
                    await refresh_card(bot, await one("SELECT * FROM orders WHERE id=?", (o["id"],)))
                    await bot.send_message(o["user_id"], cancel_notice(o, done["price"], "PESANAN BERAKHIR",
                                           "Pesanan berakhir tanpa kode OTP."), reply_markup=cancel_kb(o))
            elif d["status"] in ("COMPLETED", "EXPIRED", "CANCELED"):
                await run("UPDATE orders SET status='COMPLETED' WHERE id=? AND refunded=0", (o["id"],))
                await refresh_card(bot, await one("SELECT * FROM orders WHERE id=?", (o["id"],)))

async def poller(bot: Bot):
    while True:
        try:
            await poll(bot)
            await poll_deposits(bot)
        except Exception:
            log.exception("poll error")
        await asyncio.sleep(4)


# ---------- trafik (channel) & promosi (user): DUA alur terpisah ----------
# 1) LAPORAN TRAFIK  -> hanya ke CHANNEL. Perintah admin: /trafik (tombol "Kirim ke Channel") + jadwal otomatis TRAFFIC_TIMES.
# 2) PROMOSI         -> hanya ke USER bot. Perintah admin: /autobroadcast + jadwal otomatis PROMO_TIMES.
# Sumber data (bukan data toko):
#  - API SMSCode (provider bot ini): harga, stok, dan operator real-time per negara & layanan.
#  - API publik web (tanpa API key): success rate (SR) pasar per negara & layanan.
#    API SMSCode tidak membuka angka SR di katalognya, jadi SR diambil dari API publik 5sim.
#    Matikan dengan env MARKET_SR=0 (laporan tetap jalan, hanya tanpa angka SR).
# Negara diurutkan sesuai PRIO_COUNTRIES (PH -> ID -> BR -> CL -> ZA), operator ikut ditampilkan.
SR_API = os.getenv("SR_API_URL", "https://5sim.net/v1/guest/prices")
MARKET_SR = os.getenv("MARKET_SR", "1") != "0"
SR_SLUGS = {"PH": ("philippines",), "ID": ("indonesia",), "BR": ("brazil",),
            "CL": ("chile",), "ZA": ("southafrica", "south_africa")}          # kode negara -> slug API SR
TRAFFIC_SERVICES = [("1️⃣ Google / YouTube / Gmail", ("google", "gmail", "youtube"), "google"),
                    ("2️⃣ WhatsApp", ("whatsapp",), "whatsapp"),
                    ("3️⃣ Telegram", ("telegram",), "telegram")]              # (label, kata kunci katalog, slug API SR)
TRAFFIC_OPS = 2          # jumlah operator termurah yang ditampilkan per negara
TRAFFIC_MIN_STOCK = 5    # stok minimal agar operator/negara dianggap stabil
GOOD_SR = 50             # SR minimal (%) agar negara dianggap stabil
PROMO_COUNTRIES = ["PH", "BR", "CL", "ID"]   # negara di pesan promosi ke user (ditampilkan termurah dulu)

BROADCAST_TZ = int(os.getenv("BROADCAST_TZ", "7"))                   # jam dari UTC (WIB = 7)


def _parse_slots(raw, default):
    out = set()
    for t in str(raw).split(","):
        try:
            hh, mm = t.strip().split(":")
            if 0 <= int(hh) < 24 and 0 <= int(mm) < 60:
                out.add((int(hh), int(mm)))
        except ValueError:
            continue
    return sorted(out) or default


# Jadwal otomatis (masing-masing 3x sehari). Ubah lewat env, contoh TRAFFIC_TIMES=07:30,13:00,19:30
TRAFFIC_SLOTS = _parse_slots(os.getenv("TRAFFIC_TIMES", "08:00,14:00,20:00"), [(8, 0), (14, 0), (20, 0)])  # -> channel
PROMO_SLOTS = _parse_slots(os.getenv("PROMO_TIMES", "09:00,15:00,21:00"), [(9, 0), (15, 0), (21, 0)])      # -> user


def pick_services(services):
    """Cari Google/YouTube/Gmail, WhatsApp, dan Telegram di katalog (yang aktif)."""
    active = [s_ for s_ in services if s_.get("active")]
    out = []
    for label, keys, sr_product in TRAFFIC_SERVICES:
        svc = None
        for key in keys:
            svc = next((s_ for s_ in active if key in s_["name"].lower()), None)
            if svc: break
        out.append((label, svc, sr_product))
    return out


def split_msg(text, limit=3900):
    """Pecah teks panjang per blok agar tidak melewati batas 4096 karakter Telegram."""
    parts, cur = [], ""
    for blk in text.split("\n\n"):
        if cur and len(cur) + 2 + len(blk) > limit:
            parts.append(cur)
            cur = blk
        else:
            cur = f"{cur}\n\n{blk}" if cur else blk
    if cur: parts.append(cur)
    return parts


async def send_long(bot: Bot, chat_id, text, markup=None):
    parts = split_msg(text)
    for i, part in enumerate(parts):
        await bot.send_message(chat_id, part, reply_markup=markup if i == len(parts) - 1 else None)


# ----- SR pasar dari API publik -----
_sr_cache = {}   # slug layanan -> (berlaku sampai, {KODE_NEGARA: SR%})


def _find_ops(data, country, product):
    """Ambil {operator: {cost, count, rate}} dari respons API (tahan terhadap beda susunan JSON)."""
    if not isinstance(data, dict): return {}
    for first, second in ((country, product), (product, country)):
        node = data.get(first)
        if isinstance(node, dict):
            node = node.get(second)
            if isinstance(node, dict) and node:
                return {k: v for k, v in node.items() if isinstance(v, dict)}
    return {}


def _weighted_sr(ops):
    """SR rata-rata tertimbang stok dari semua operator yang masih punya stok. None jika tidak ada data."""
    pts = []
    for v in ops.values():
        try:
            rate, cnt = float(v.get("rate")), float(v.get("count") or 0)
        except (TypeError, ValueError):
            continue
        if cnt > 0: pts.append((min(100.0, max(0.0, rate)), cnt))
    if not pts: return None
    return round(sum(r_ * c_ for r_, c_ in pts) / sum(c_ for _, c_ in pts))


async def market_sr(product):
    """SR pasar (%) per negara prioritas untuk satu layanan. Di-cache 30 menit (5 menit jika gagal)."""
    if not MARKET_SR: return {}
    hit = _sr_cache.get(product)
    if hit and time.time() < hit[0]: return hit[1]
    out = {}
    for code, slugs in SR_SLUGS.items():
        for slug in slugs:
            try:
                async with http.get(SR_API, params={"country": slug, "product": product},
                                    timeout=aiohttp.ClientTimeout(total=10)) as resp:
                    if resp.status != 200: continue
                    data = await resp.json(content_type=None)
            except Exception as e:
                log.warning("SR API gagal (%s/%s): %s", slug, product, e)
                continue
            sr_ = _weighted_sr(_find_ops(data, slug, product))
            if sr_ is not None:
                out[code] = sr_
                break
    _sr_cache[product] = (time.time() + (1800 if out else 300), out)
    return out


def sr_label(s_):
    return "" if s_ is None else f" · SR {s_}%" + (" 🔥" if s_ >= 60 else "")


# ----- pengumpulan data trafik -----
async def traffic_block(label, svc, sr_product, by_code):
    """Satu blok layanan. Return (teks, jumlah negara yang ada stoknya, pilihan terbaik atau None)."""
    if not svc:
        return f"<b>{esc(label)}</b>\n└ <i>Layanan tidak ditemukan di katalog</i>", 0, None
    products = await cached("/catalog/products", {"platform_id": svc["id"], "sort": "price_asc", "limit": 10000}, ttl=60)
    stock = {}
    for p in products:
        if p.get("active", True) and p.get("available", 0) > 0:
            stock.setdefault(p["country_id"], []).append(p)
    sr = await market_sr(sr_product)
    lines, best, ready = "", [], 0
    for idx, code in enumerate(PRIO_COUNTRIES):
        c = by_code.get(code)
        if not c: continue
        flag, name = c.get("emoji") or "🌍", esc(c.get("name", code))
        offs = stock.get(c["id"])
        if not offs:
            lines += f"🔴 {flag} <b>{name}</b> — stok habis\n"
            continue
        ready += 1
        s_ = sr.get(code)
        ops = {}  # operator -> harga modal termurah + total stok operator itu
        for p in offs:
            nm = p.get("operator_name") or "Any"
            o = ops.setdefault(nm, {"price": p["price"], "stock": 0})
            o["price"] = min(o["price"], p["price"])
            o["stock"] += p["available"]
        # operator dengan stok cukup dulu (lebih stabil), lalu yang termurah
        ranked = sorted(ops.items(), key=lambda it: (it[1]["stock"] < TRAFFIC_MIN_STOCK, it[1]["price"], -it[1]["stock"]))
        total = sum(o["stock"] for o in ops.values())
        solid = total >= TRAFFIC_MIN_STOCK
        emo = "🔴" if s_ is not None and s_ < 20 else "🟢" if solid and (s_ is None or s_ >= GOOD_SR) else "🟡"
        lines += f"{emo} {flag} <b>{name}</b>{sr_label(s_)} · stok {total}\n"
        for nm, o in ranked[:TRAFFIC_OPS]:
            lines += f"   📡 <code>{esc(nm)}</code> · <b>{rp(sell_price(o['price'], c))}</b> · stok {o['stock']}\n"
        top_nm, top = ranked[0]
        stable = solid and top["stock"] >= TRAFFIC_MIN_STOCK and ((s_ is not None and s_ >= GOOD_SR) if sr else True)
        if stable:
            best.append((sell_price(top["price"], c), idx, flag, name, top_nm))
    pick = min(best) if best else None
    head = f"<b>{esc(label)}</b>\n"
    if pick:
        head += f"🏆 <i>Paling hemat &amp; stabil:</i> {pick[2]} <b>{pick[3]}</b> · <code>{esc(pick[4])}</code> · <b>{rp(pick[0])}</b>\n"
    return head + (lines or "└ <i>Negara prioritas belum tersedia di katalog</i>\n").rstrip("\n"), ready, pick


async def collect_traffic():
    """Ambil data 3 layanan. RuntimeError jika katalog kosong / tidak ada stok (agar tidak kirim laporan kosong)."""
    services = await cached("/catalog/services", ttl=600)
    if not services:
        raise RuntimeError("Data katalog belum bisa diambil dari API. Coba lagi sebentar.")
    by_code = {str(c.get("code", "")).upper(): c for c in await cached("/catalog/countries", ttl=600) if c.get("active")}
    rows, ready = [], 0
    for label, svc, sr_product in pick_services(services):
        text, n, pick = await traffic_block(label, svc, sr_product, by_code)
        rows.append((label, text, pick))
        ready += n
    if not ready:
        raise RuntimeError("Tidak ada stok di negara prioritas saat ini.")
    return rows


# ===== ALUR 1: laporan trafik -> channel =====
async def get_traffic_report(admin=False):
    rows = await collect_traffic()
    blocks = ["🔥 <b>REKOMENDASI TRAFIK OTP · TERMURAH &amp; STABIL</b>\n" + LINE + "\n"
              "<i>Prioritas negara: PH → ID → BR → CL → ZA. Operator diurutkan yang stoknya cukup &amp; termurah dulu.\n"
              "SR = tingkat sukses OTP pasar. 🟢 bagus · 🟡 sedang · 🔴 rendah/habis</i>"]
    blocks += [text for _, text, _ in rows]
    if admin:
        blocks.append("ℹ️ <i>Sumber: API SMSCode (harga, stok, operator) + API publik (SR pasar). Bukan data transaksi toko.</i>")
    return "\n\n".join(blocks)


async def post_traffic_channel(bot: Bot):
    """Kirim laporan trafik ke channel. Error jika CHANNEL_ID kosong."""
    if not CHANNEL_ID:
        raise RuntimeError("CHANNEL_ID belum diisi di Variables Railway.")
    text = await get_traffic_report()
    me = await bot.get_me()
    link = kb([[InlineKeyboardButton(text="🛒 Beli Nomor di Bot", url=f"https://t.me/{me.username}")]])
    await send_long(bot, CHANNEL_ID, text, link)


async def traffic_job(bot: Bot):
    if not CHANNEL_ID: return
    await post_traffic_channel(bot)
    log.info("Laporan trafik terkirim ke channel.")


# ===== ALUR 2: promosi -> user =====
# Kata-kata promosi untuk user (dipilih acak tiap kirim, supaya tidak monoton).
# Hanya klaim yang benar sesuai cara kerja bot: bayar QRIS, saldo otomatis, pesanan tanpa OTP dibatalkan & saldo kembali.
def promo_opening():
    return random.choice([
        "🔥 <b>NOMOR OTP TERMURAH: FILIPINA, BRAZIL, CHILE &amp; INDONESIA</b>\n"
        "Harga di bawah diambil real-time dari sistem, bukan harga lama. Bandingkan sendiri, lalu pilih yang paling pas.",
        "💸 <b>CARI NOMOR OTP HEMAT? INI HARGA TERMURAH HARI INI</b>\n"
        "Kami rangkum harga paling murah per layanan di 4 negara favorit. Tinggal pilih, tidak perlu keliling cek satu-satu.",
        "📣 <b>HARGA TERMURAH OTP, UPDATE TERBARU</b>\n"
        "Google, WhatsApp, Telegram: cek harga mulai dari berapa di Filipina, Brazil, Chile, dan Indonesia.",
        "⚡ <b>JANGAN BELI BUTA, LIHAT HARGANYA DULU</b>\n"
        "Ini daftar harga termurah saat ini untuk 4 negara paling dicari. Yang termurah ditandai 🏆.",
    ])


def promo_closing():
    mins = max(1, AUTO_CANCEL // 60)
    return random.choice([
        f"💬 <b>Masih ragu?</b> Coba 1 nomor dulu. Top up mulai {rp(MIN_DEP)} via QRIS, saldo masuk otomatis. "
        f"Kalau OTP tidak masuk dalam {mins} menit, pesanan dibatalkan dan saldo kembali otomatis, jadi risikonya kecil.",
        "🛡 <b>Beli tanpa was-was:</b> bayar QRIS, saldo masuk otomatis, biaya admin top up ditampilkan jelas sebelum kamu bayar. "
        "OTP tidak masuk? Saldo kembali otomatis.",
        "🤝 Kami lebih suka kamu mencoba daripada hanya percaya janji. Ambil satu nomor, lihat sendiri OTP-nya masuk. "
        "Kalau gagal, pesanan dibatalkan dan saldo balik otomatis.",
        f"⏱ Daftar harga ini diperbarui otomatis {len(PROMO_SLOTS)}x sehari. "
        "Tinggal pilih layanan, negara, operator, selesai dalam hitungan menit.",
    ])


async def promo_service_prices(svc, by_code):
    """Harga jual TERMURAH per negara promosi (PROMO_COUNTRIES) untuk satu layanan.
    Return [(harga, emoji, nama negara)] urut termurah. Negara tanpa stok dilewati.
    Penawaran dengan stok >= TRAFFIC_MIN_STOCK diutamakan agar harga murah yang tampil tidak cuma 1-2 nomor."""
    products = await cached("/catalog/products", {"platform_id": svc["id"], "sort": "price_asc", "limit": 10000}, ttl=60)
    stock = {}
    for p in products:
        if p.get("active", True) and p.get("available", 0) > 0:
            stock.setdefault(p["country_id"], []).append(p)
    out = []
    for code in PROMO_COUNTRIES:
        c = by_code.get(code)
        offs = stock.get(c["id"]) if c else None
        if not offs: continue
        pool = [p for p in offs if p["available"] >= TRAFFIC_MIN_STOCK] or offs
        top = min(pool, key=lambda p: p["price"])
        out.append((sell_price(top["price"], c), c.get("emoji") or "🌍", esc(c.get("name", code))))
    return sorted(out)


async def get_promo_text():
    """Pesan promosi: ajakan + harga termurah per layanan di PH, BR, CL, ID (data real-time) + penutup untuk yang ragu."""
    services = await cached("/catalog/services", ttl=600)
    if not services:
        raise RuntimeError("Data katalog belum bisa diambil dari API. Coba lagi sebentar.")
    by_code = {str(c.get("code", "")).upper(): c for c in await cached("/catalog/countries", ttl=600) if c.get("active")}
    blocks, found = [promo_opening()], 0
    for label, svc, _ in pick_services(services):
        if not svc: continue
        rows = await promo_service_prices(svc, by_code)
        if not rows: continue
        found += 1
        lines = [f"<b>{esc(label)}</b>"]
        for i, (price, flag, name) in enumerate(rows):
            lines.append(f"{'🏆' if i == 0 else '▫️'} {flag} {name} · <b>{rp(price)}</b>")
        blocks.append("\n".join(lines))
    if not found:
        raise RuntimeError("Tidak ada stok di Filipina, Brazil, Chile, dan Indonesia saat ini.")
    blocks.append("<i>Harga &amp; stok bisa berubah sewaktu-waktu mengikuti ketersediaan.</i>")
    blocks.append(promo_closing())
    return "\n\n".join(blocks)


async def promo_enabled():
    row = await one("SELECT value FROM settings WHERE key='promo_on'")
    return row is None or row["value"] != "0"          # default: aktif


async def set_promo_enabled(on):
    await run("INSERT OR REPLACE INTO settings(key,value) VALUES('promo_on',?)", ("1" if on else "0",))


async def _send_user(bot: Bot, uid, parts, markup, errs=None):
    """Kirim ke satu user. Return 'ok' / 'blocked' / 'failed'. Menunggu otomatis jika kena batas Telegram."""
    for attempt in (1, 2):
        try:
            for i, part in enumerate(parts):
                await bot.send_message(uid, part, reply_markup=markup if i == len(parts) - 1 else None)
            return "ok"
        except TelegramRetryAfter as e:
            await asyncio.sleep(float(getattr(e, "retry_after", 5)) + 1)
        except TelegramForbiddenError:
            return "blocked"
        except Exception as e:
            log.warning("Promo ke %s gagal: %s", uid, e)
            if errs is not None: errs.append(str(e)[:90])
            return "failed"
    return "failed"


async def do_promo(bot: Bot):
    """Kirim promosi ke SEMUA user bot (yang pernah /start). Tidak mengirim apa pun ke channel."""
    parts = split_msg(await get_promo_text())      # RuntimeError jika data kosong -> tidak ada yang dikirim
    menu = kb([[b("🛒 Beli Nomor Sekarang", "hm")]])
    res = {"ok": 0, "blocked": 0, "failed": 0, "errors": []}
    for row in await fetch("SELECT id FROM users"):
        res[await _send_user(bot, row["id"], parts, menu, res["errors"])] += 1
        await asyncio.sleep(0.06)  # ±16 pesan/detik, aman dari batas Telegram
    return res


async def promo_job(bot: Bot):
    if not await promo_enabled():
        log.info("Auto broadcast promosi nonaktif, jadwal dilewati.")
        return
    log.info("Promosi ke user selesai: %s", await do_promo(bot))


def promo_summary(res):
    total = res["ok"] + res["blocked"] + res["failed"]
    txt = (f"📢 <b>Promosi selesai</b>\nTarget: {total} user (semua yang pernah /start)\n"
           f"✅ terkirim {res['ok']} · 🚫 blokir bot {res['blocked']} · ❌ gagal {res['failed']}")
    if res.get("errors"):
        from collections import Counter
        txt += "\n\nAlasan gagal:\n" + "\n".join(f"• {esc(m)} ({n}x)" for m, n in Counter(res["errors"]).most_common(3))
    return txt


# ----- penjadwal (dipakai untuk kedua alur) -----
def next_slot(now, slots):
    """Waktu terjadwal berikutnya (> now)."""
    for day in (0, 1):
        for hh, mm in slots:
            t = (now + timedelta(days=day)).replace(hour=hh, minute=mm, second=0, microsecond=0)
            if t > now: return t


async def run_schedule(name, slots, job, bot: Bot):
    tz = timezone(timedelta(hours=BROADCAST_TZ))
    log.info("Jadwal %s aktif: %s (UTC%+d)", name, ", ".join(f"{h:02d}:{m:02d}" for h, m in slots), BROADCAST_TZ)
    while True:
        nxt = next_slot(datetime.now(tz), slots)
        while True:
            left = (nxt - datetime.now(tz)).total_seconds()
            if left <= 0: break
            await asyncio.sleep(min(left, 60))
        try:
            await job(bot)
        except Exception as e:
            log.warning("Jadwal %s dilewati: %s", name, e)


# ===== perintah admin: /trafik (channel) =====
@r.message(Command("trafik"))
async def cmd_trafik(m: Message):
    if m.from_user.id not in ADMINS: return
    loading = await m.answer("🔍 Mengambil data trafik dari API...")
    try:
        parts = split_msg(await get_traffic_report(admin=True))
    except Exception as e:
        log.warning("trafik gagal: %s", e)
        return await loading.edit_text(f"❌ Gagal membuat laporan: {esc(e)}")
    markup = kb([[b("📡 Kirim ke Channel", "send_chan")]])
    await loading.edit_text(parts[0], reply_markup=markup if len(parts) == 1 else None)
    for i, part in enumerate(parts[1:], 1):
        await m.answer(part, reply_markup=markup if i == len(parts) - 1 else None)


@r.callback_query(F.data == "send_chan")
async def send_chan_callback(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMINS: return await cb.answer("Khusus admin.", show_alert=True)
    if not CHANNEL_ID:
        return await cb.answer("CHANNEL_ID belum diisi di Variables Railway!", show_alert=True)
    try:
        await post_traffic_channel(bot)
        await cb.answer("✅ Berhasil dikirim ke channel!", show_alert=True)
    except Exception as e:
        await cb.answer(f"Gagal kirim: {e}"[:190], show_alert=True)


# ===== perintah admin: /autobroadcast (promosi ke user) =====
async def autobroadcast_panel():
    on = await promo_enabled()
    users = (await one("SELECT COUNT(*) c FROM users"))["c"]
    sched = ", ".join(f"{h:02d}:{m:02d}" for h, m in PROMO_SLOTS)
    text = (f"📢 <b>AUTO BROADCAST PROMOSI</b>\n{LINE}\n"
            f"Status: {'🟢 AKTIF' if on else '⏸ NONAKTIF'}\n"
            f"Jadwal: {sched} (UTC{BROADCAST_TZ:+d})\n"
            f"Target: {users} user (semua yang pernah /start)\n\n"
            "<i>Isi: harga termurah per layanan di PH, BR, CL, ID + ajakan untuk yang masih ragu. "
            "Hanya ke user. Laporan trafik ke channel diatur lewat /trafik.</i>")
    markup = kb([[b("⏸ Matikan" if on else "▶️ Aktifkan", "ab_toggle")],
                 [b("👁 Preview", "ab_prev"), b("📢 Kirim Sekarang", "ab_now")]])
    return text, markup


async def _show_panel(cb: CallbackQuery):
    text, markup = await autobroadcast_panel()
    try:
        await cb.message.edit_text(text, reply_markup=markup)
    except TelegramBadRequest:
        pass  # isi sama persis


@r.message(Command("autobroadcast"))
async def cmd_autobroadcast(m: Message):
    if m.from_user.id not in ADMINS: return
    text, markup = await autobroadcast_panel()
    await m.answer(text, reply_markup=markup)


@r.callback_query(F.data.startswith("ab_"))
async def autobroadcast_callback(cb: CallbackQuery, bot: Bot):
    if cb.from_user.id not in ADMINS: return await cb.answer("Khusus admin.", show_alert=True)
    act = cb.data
    if act == "ab_toggle":
        await set_promo_enabled(not await promo_enabled())
        await cb.answer("Status diubah.")
        await _show_panel(cb)
    elif act == "ab_back":
        await cb.answer()
        await _show_panel(cb)
    elif act == "ab_prev":
        try:
            text = await get_promo_text()
        except Exception as e:
            return await cb.answer(f"Gagal: {e}"[:190], show_alert=True)
        await cb.answer()
        await cb.message.answer("👁 <b>Preview promosi</b> (hanya dikirim ke kamu):\n\n" + text)
    elif act == "ab_now":
        users = (await one("SELECT COUNT(*) c FROM users"))["c"]
        await cb.answer()
        await cb.message.edit_text(f"⚠️ Kirim promosi ke <b>{users} user</b> sekarang?",
                                   reply_markup=kb([[b("✅ Ya, kirim", "ab_go"), b("‹ Batal", "ab_back")]]))
    elif act == "ab_go":
        await cb.answer("⏳ Mengirim, tunggu ringkasannya...")
        await _show_panel(cb)
        try:
            await cb.message.answer(promo_summary(await do_promo(bot)))
        except Exception as e:
            await cb.message.answer(f"❌ Promosi gagal: {esc(e)}")
    else:
        await cb.answer()


# ===== backup & restore database (admin) =====
BACKUP_HOURS = float(os.getenv("BACKUP_HOURS", "24"))   # backup otomatis ke admin tiap N jam; 0 = mati


async def make_backup_file():
    """Salinan database yang konsisten (VACUUM INTO) di folder sementara."""
    await db.commit()
    path = os.path.join(tempfile.gettempdir(), f"store_backup_{int(time.time())}.db")
    if os.path.exists(path): os.remove(path)
    await db.execute("VACUUM INTO ?", (path,))
    return path


async def send_backup(bot: Bot, chat_id: int, auto: bool = False):
    path = await make_backup_file()
    try:
        n = (await one("SELECT COUNT(*) c FROM users"))["c"]
        stamp = datetime.now(WIB).strftime("%Y%m%d_%H%M")
        cap = (f"💾 <b>Backup database</b>{' (otomatis)' if auto else ''}\n"
               f"{n} user • {datetime.now(WIB).strftime('%d %b %Y %H:%M')} WIB\n"
               f"<i>Simpan file ini. Untuk memulihkan: kirim file ini ke bot dengan caption /restore</i>")
        await bot.send_document(chat_id, FSInputFile(path, filename=f"store_{stamp}.db"), caption=cap)
    finally:
        try: os.remove(path)
        except OSError: pass


@r.message(Command("backup"))
async def cmd_backup(m: Message, bot: Bot):
    if m.from_user.id not in ADMINS: return
    try:
        await send_backup(bot, m.chat.id)
    except Exception as e:
        log.exception("backup gagal")
        await m.answer(f"❌ Backup gagal: {esc(e)}")


def _validate_db(path: str):
    """Pastikan file adalah database SQLite yang valid dan punya tabel users."""
    c = sqlite3.connect(path)
    try:
        if c.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
            return "Database rusak (integrity_check gagal)."
        names = {x[0] for x in c.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if "users" not in names:
            return "Bukan database bot ini (tabel users tidak ada)."
        return None
    except sqlite3.DatabaseError as e:
        return f"File bukan database SQLite yang valid: {e}"
    finally:
        c.close()


@r.message(F.document, F.caption.startswith("/restore"))
async def cmd_restore_file(m: Message, bot: Bot):
    global db
    if m.from_user.id not in ADMINS: return
    tmp = os.path.join(tempfile.gettempdir(), f"restore_{int(time.time())}.db")
    try:
        await bot.download(m.document, destination=tmp)
        err = await asyncio.to_thread(_validate_db, tmp)
        if err: return await m.answer(f"❌ {esc(err)}")
        await db.commit()
        await db.close()
        for ext in ("-wal", "-shm"):
            if os.path.exists(DB_PATH + ext): os.remove(DB_PATH + ext)
        shutil.copyfile(tmp, DB_PATH)
        db = await aiosqlite.connect(DB_PATH)
        db.row_factory = aiosqlite.Row
        await init_db()
        n = (await one("SELECT COUNT(*) c FROM users"))["c"]
        await m.answer(f"✅ Database dipulihkan. {n} user terdaftar.")
    except Exception as e:
        log.exception("restore gagal")
        try:
            db = await aiosqlite.connect(DB_PATH); db.row_factory = aiosqlite.Row
        except Exception: pass
        await m.answer(f"❌ Restore gagal: {esc(e)}")
    finally:
        try: os.remove(tmp)
        except OSError: pass


@r.message(Command("restore"))
async def cmd_restore_help(m: Message):
    if m.from_user.id not in ADMINS: return
    await m.answer("Kirim file backup <code>.db</code> ke chat ini, lalu isi <b>caption</b>-nya dengan <code>/restore</code>.\n"
                   "⚠️ Data saat ini akan <b>diganti</b> isi file tersebut.")


async def backup_loop(bot: Bot):
    if BACKUP_HOURS <= 0: return
    log.info("Backup otomatis ke admin tiap %s jam", BACKUP_HOURS)
    while True:
        await asyncio.sleep(BACKUP_HOURS * 3600)
        for a in ADMINS:
            try: await send_backup(bot, a, auto=True)
            except Exception as e: log.warning("Backup otomatis ke %s gagal: %s", a, e)


async def main():
    global db, http
    os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)
    db = await aiosqlite.connect(DB_PATH)
    db.row_factory = aiosqlite.Row
    await init_db()
    _n = (await one("SELECT COUNT(*) c FROM users"))["c"]
    log.info("Database: %s (%s user terdaftar)", os.path.abspath(DB_PATH), _n)
    http = aiohttp.ClientSession()
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    err = await check_channel(bot)
    log.info("Monitoring channel: %s", "nonaktif (CHANNEL_ID kosong)" if not CHANNEL_ID else (err or "OK"))
    if err:
        for a in ADMINS:
            try:
                await bot.send_message(a, f"⚠️ Monitoring channel belum siap: {esc(err)}")
            except Exception:
                pass
    dp_ = Dispatcher(storage=MemoryStorage())
    dp_.include_router(r)
    runner = None
    if KASERA_KEY and WH_SECRET:
        app = web.Application()
        app["bot"] = bot
        app.router.add_post("/kasera/webhook", kasera_webhook)
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, "0.0.0.0", WEBHOOK_PORT).start()
        log.info("Webhook Kasera aktif di port %s", WEBHOOK_PORT)
    task = asyncio.create_task(poller(bot))
    ttask = asyncio.create_task(run_schedule("trafik-channel", TRAFFIC_SLOTS, traffic_job, bot))
    ptask = asyncio.create_task(run_schedule("promo-user", PROMO_SLOTS, promo_job, bot))
    btask = asyncio.create_task(backup_loop(bot))
    try:
        await dp_.start_polling(bot)
    finally:
        if runner: await runner.cleanup()
        task.cancel()
        ttask.cancel()
        ptask.cancel()
        btask.cancel()
        await http.close()
        await db.close()

# Banner robot UMKM OTP (JPEG, base64). Boleh ditimpa dengan file robot_banner.jpg di folder yang sama.
BANNER_B64 = "/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAYEBQYFBAYGBQYHBwYIChAKCgkJChQODwwQFxQYGBcUFhYaHSUfGhsjHBYWICwgIyYnKSopGR8tMC0oMCUoKSj/2wBDAQcHBwoIChMKChMoGhYaKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCj/wAARCALQAtADASIAAhEBAxEB/8QAHAAAAAcBAQAAAAAAAAAAAAAAAAECAwQFBgcI/8QAXxAAAQMDAQQGBgUGCAkKBQIHAQACAwQFESEGEjFBBxMiUWFxFDKBkaGxI0JSwdEVM2Jy4fAIFiRDgpKTsiZEU2NzdKKz0hclNFRVZIOUwvEnNjdFdTVloxhGhIXTw//EABsBAAEFAQEAAAAAAAAAAAAAAAABAgMEBQYH/8QAOREAAgICAQMDAwIFAwMEAgMAAAECAwQRIQUSMRNBUSIyYQYUI0JxkaEVgbEWM1IkNHLBQ2LR4fD/2gAMAwEAAhEDEQA/APMQR4RhBXCAII0EEgAQQQQAMao8IIspQAggjAQAEMI0EAFhDCNBABYRlBBAAQQQS6ACCCGEABABHjCMJQCwjQQQI2BBBBJoQCCCNKgCQSgglAJDCNBIAWEEaCAAgghhKAEEaCAAiSkEAEgggkAPCLCNBKAWEMI8IsIAGEEEEAFhHhBGgBKCNBABII0MIAJBDCGEABFhGggAsIYRoJAEoJSLCNgEhyQQQACgiQSAAoAII8IFTEkII0EChIIFBAARAI0EaAJDCNEkAGEMI0EAFhDCNBACUSUUWEoBIIwlJAEYQwloIDYnCJLSXIAJAII0AEEaAQQAEEEEgAQQQSgBBBGgAI0EEABBBBIAEEEEugAgggnABBBGgAsI0MI8pBNgRIFBKIBGgEEABGhhGgAsI0EEABBBHhABIYSsIIALCCPCACUAkErCGEgBYRgII0oBYQwlYPNDd8UBoThDCVhFhAugsIYS8IvYgNCUErHghjwQGhKCVjwQ0QGhOEMJWEWEBoLCLdSt3xQxogNCSEWErVBAglBKRJACQwlYSSlAGESNBABFBGiwkACIhGgjQCSESWiwgBKCMhEgA0SPKJIAEWEaCBUwkEOKCBQIIIIACCCCAAgggkACCCCUAiEAjREJADQSQlIEAiRoJACOEkpR4JKUUNBAI8JACQR4RJQAggEaAAjQQQAEEEEgAQQQS6ACCCJKAaCARpQAEaJBII2GUSCCUQCMBDCMBAAARoIIACCCNKASPCGEeEAAcEEYCNJsAsIYRoYS6DQEEeAjwgckFhABKwhhDF7QgjwlYR4RsXtG8I8JYalbqTY7tG8It1O7iPcSbHdg1hDdTu4j3EdwvpjO74Ibqe3ENxGw9MZIRbqf3EW4jYnpjOEMJ3cQ3UbE7BrCLCd3UW6l2hOwbwiwnN1Fuo2hriIwiwl4REJRO0Si0SsIYQJoSQiwlY7kMJBNCEaUk4KNiBIsI0EoBIIYQQAERCNBJoBOESUiIQASCCCAAhhBBIGwkEZRIHAQQQSgBBBBIAEEEEABBBBIARCGUaLCAAEaSClIEAkkapSSUgqAEpEECUoAyiQRhAAARoIIACCCCQAIIIJUAEEEE4AI8II0gBI+CCJA0CCCNABIwEYCNKAECggEaACPCMIJQCRhHhGkALCCNGEC6CwjwjRgJRyQQGiGClgJW6k2OURG6jwnA1KDUmx6gxoNylbqdDUsMTXIkVYyGpQangxLDE3uJVSMBiPcUgMRhib3kipI+4jDFJDEe4juJFQRtxDqypQjShGk7h3osidWUNwqYIkfVeCO4PRIW4iLFNMXgkmNHcHokPcRFillngiLPBHcNdJD3EncUwsSdwJe4jdJE3ERapRYiLE5SI3URC1JLVKLUgsTu4jdZHISSE+WapJal2ROAzhDCcISSNE5MY4iCERSsIYQNaGyhhLIScI0N0JwglFEQgQIhEjQSgEiRoJAEkIYRoaIASgjRJAAgggjQARI0EDgkEEEABBBBAAQQQSABBBBABEIhxSkkoAUkFAFBABhBAIJQDARoIJGAEEEEgAQQQSgBBBBKAAjCCCADRIIIGgQRhDCABhGEeEEoAQQCCUAI0EeEAAI8IBGkFSBhKwiCUBlKOSCRgJQCUGpGx6gJASg1LDU41iY5EsaxsNSwxOtYnGsTHInjUMhiWGJ4MSxGmuRYjQMBicaxPCNOwwvlcGxsc93c0E/JN234JlUo+SOI0sRq5hsNe8AvhbC085nhvw4qdDYYG61Fbvfowx5+JUkaLJ+ERzysar7pGaEfgj3BzWvjtltj/mJpj3ySYHuCksbTxY6mipWY59XvH4qeODY/L0VZdWoj9sWzEsjLzhrS4/ojKlRWutl/N0dQ7yjK2TaucaMeWDuYA35IGeV/rSvPm4qVYHyyvLrT/lgZiPZ+5O40Uo/WwPmVJj2auJ4wMb+tK0fer9ozx181Lgi3sDCX9lBe4R6pfPwkZtuzFf9iD+3Z+KWdl67Hqwf2zfxWvipsjJ4I304xkHTwTf29fjZJ+7yHzwYmTZm4jhAx36sjT96jSbPXMf4lKfLB+9bSaHdGVFdodNPJP8A2UJeGRS6pdB8pGMls9fGO3RVLf8AwioUsD4z9IxzD+k0hdBbNK31ZXjycU56ZUEYdKXDucN75pjwPhirrT/mgc1LQeCLc8F0WUU8w/lFFSy+JiAPvCiyWi0y+tTSwnvhlz8Co3g2LwyaHV6JfcmjBGPwSTGtpNsxSP1pbgWZ+rPF94UCo2XuLWkwRx1LRzgeHH3cVDKiyPsWoZWNb4kZgsSCxWNTSTUz9yoikid3SNLfmmHRqLbXkm9JS5jyQnM8E2WKa5iQ5iVSIJUEFzEgtU1zE05ikUyCVJFLUktUhzEgtTlIglXoYIRYTpaklqensicRvCSlkIkozQkhFhKwiQMaEoIyESACQKBRIAJEQlIkmgCQR4QSAEggggAIijKCB2wkEEEABBBBAAQQQSABAoIIASQiS0goAPijRDilIACCCCQAIIIJQAggglFAjQQQI2GESCCUaBBGAjHFABAJSCMIALCGErCLCUABDCMBGEaAACPCAylAIHaCASgMo2tS8ZQPURIGiUGpxrEsMTGyaNextrfBONYnGsTrWKJyLMKhprPBONYnmxpYjwmORahSNNZ4J1rPBWNDaamqaHhrYof8rKd1v7fYrent1DTAFwfVyD7XYZ7uJUtdFlnhEduXRR5e2Z+lpJamTcp4nyv7mDKtoLA8DNZURQfoN7b/AHDQe9XBqZOr6thEcXJkY3W/BNDgrteDFczezLu6xOXFa0Nw0Fvp8bsDqh4+tO7T+qFMFTI1u5EREz7MTQwfBMBHoNeStxqhDwjMsvss5k9is5OSck80YJUSavpYTiSZu93DU/BQ5b0wfmYJH+LuyE52Rj5YkKLJ/ai6ByhrlZyW7VbtG9TGPAbyjPq6mT16mQjuBAUMsqtFyHS75eVo1mccSB5ojUQs9eaNvm4LHktJ+kc5x/ScSlNMQ+oFE8xeyLUOjy/mkjYx19GONTF71dWiemq6iGngf1k0rxGxjQcucTgD3rncUrRwAHkFuuiqpj/j7YBMewaoAZ+1g7vxwq1uXL2RoU9LhCLl3eD0NsxsfbLWxrJYIayuA+lmlbvtaeYY06ADv4lW922RtVxpSKmhgGRpLCwRSM8QRx8jlM2mq6uV4kPaDjkHzV7Nc2NpyBxwsb95LubbEsxnFpRR5t22t7Nm7tLRVszSQA+OTBAkYeDvDxHIgrIyXGicezUx+04W8/hBVbHXKztOOuFK8u/VMnZ+9cXmlbnUBbFWZJLwEulxth3OWmaptVTvPZniPk4J5pDvVIPkcrDOdGfqg+xECxpy0uafBxCsrMXuijPoz/lkbzzRrEx1lVH+bq5gPF2981KivdwYdXQyj9JuPkpY5VbKs+lXx8LZrEQ0IPPvVDDtEP8AGKV48Y3bwU+nvNFOQGzhpPJ43VMrIy8MpTxra/uiW4qpur6t7hJH9iUB49xUGottrqsmWk6h5+vTu3f9k6J5rg9uWkOHeEaSVUJrlCV32VP6XoparZV7gTb6qOf/ADcn0b/wPvVDXW6qopNyrp5IXfpjAPtW5CfbUytjMZIkiPGOQBzT7CqtmDF8x4NOnrFkeLFs5k6PwTLmeC6FVWa11oOGPopT9aLtMPm06j2KguezddSMdLG1tTTj+dg7QHmOIVGzHsr8mpVmUX8J6f5Mw5ngmyxTnMzw4JsxqJSJp0EFzU25qmuYmnMUikVJ1EMtSS1SXNTbmqRMryhoYIRJ0tSCE7ZA4iEkhLREI0NaEFElkJOEo0JJS0khAARI0MJGASIpRCJIASAQQQwAUnglIikHIIo0RQCUUNBBBIIBBBBAASSlJLggUMI0QRoEAggggAIIIJQAjCAQQACggggaBAIYSmhAAAwjQRgJwAA1SgEAE41hKVIRsRjRABPiModWU7tETGQEAE91aAYjQ9MbAS2hOBicbGhokS2NtYnGsT0cRKkMhKZJFiESM2NOCNS2wHuTrYD3KCWy9XXshtjTrWeCsKS3TVTiIWdkcXOOGjzKtqekpqMggNqJx9dw7A8hz8yiuidr/AX5VOMvqe38FXR2monYJHAQwf5STQHyHE+xW1PT0lJ+YhEso/nZhn3N4D2o5JXyv35HFzu8lECtKnEhX55Zh5PUrbuE9IdkkfK7ekeXHkSkpt8jI2F0jg1o5kqFNcwcinj3v03aBWJTjBcspwqna9RWyz8TwUWW5U8WQHGR3czVU08skv5+Vzh9kaN9yjvmYwYGAO4aKrPLS+01Kekvza9FpNdZ3aQsbEO93aKhTSvl1mlfJ5nA9yap4qqtOKSnklH2gMNHtOitaTZirmw6qnZE08mDeP4Kjbm6+6Rt4nRnL/tV7/LKkysbwwPJNGpDjhvaPcNStrR7JUTMGSN8x75HZHuGivKWzxRNAiiZGO5rQPkqEs+Pstm5V0K3+eSRzaKiuFRrFSS473DdHxU6HZ64S46x0MXtLvkujstw4kKZT2t0hAiie89zWkqGWbY/Bcj0jGhzOTZzqHZN5/O1bz+ozHzKmw7J0w9d9Q/zcB8gul0+zdbIOzRyDxdhvzVhDsjWu4siZ5v/AAUTutfuSqjBr9kcxi2YoQdYXnzkcrKislLTyxSww7kkbg9jg45a4HII1710Zux8zfzlRAz2Ep0bLRMH0lwhb7B+Kb3WPyyRW4keFFf2Jf8AHKA2qeuqwYqqnj6ycNGkgGMub7+Cmt2pgZQwVNUXhk8LJoo2jtPa4Egdw4a54LG7bWenotjb3PFXxyvbSlu4N3OrmjOhVhQ2+CvtFl9Iqm0+7a6cguI7R7Q5+SsqhSqdvuc/bOqOXGiP2v8AuZHaxjdobtPX18DTI8BrW5OGMGgaPJZifZuidndhc3yeV1r+LVPIOxcoXewfiidsc535urhd/RKq9017m+rMRRUXFaX4OLzbL0+Tumdvk9QZtmSPzdRIP1mgrt02xVYAd3qH/wBIj5hV1RslXM/xRzv1CHJ6utXuN9LAs8xRxWWyVsRPVyRPHtCiSU1bDq+B+O9va+S67V2KWL87Tys/WYQquW0g+q0ZUizLF55IpdJxbPsk1/ucw9K3Dh4LT3OGCliVkgwQCt7U2ZrshzA79YZVNVbNwE5bGWO72HH7FPDOj7rRSt6JZ/JJP+pQ08r4TmmmfF+q7Q+xWtNfayIATMjnb/VKhT2Oph1hkDx3PGCoUraimP08L2j7XEe8K/Vmb+2RiZXR9f8Adr1+Ua6lv1HMQ2Vxgf3SDA96tGSNe0Oa4OaeBByCuesnZI3B1HipFNLJTHepZnR+AOh9iuwzF/MjEu6Q/NTN2lRSvifvROcx3e04WapNoHtwK2HI+3H94V3S1UNUzep5GvGNQDqPYrcZxmuGZNlFlL1JaHqyloLln06mDJj/AIxTjdd/SbwKzd02Zq6WN01MRWUo+vCDlv6zeIWlwlxSvhkEkT3MeODmnBVe3FhMt4/UbaeN7RzhzEy9i6NcKGguuXVLBS1Z/wAYhbo79Zv3hZO8WSrtha6oY10L/UmjO8x3t5HwKzrKJ1s3KMurJXHDM+5iaexTnxplzFGmLZUQnNSC1S3MTbmKVMqTrIpakEKQWpBapEV5R0M4yEkhPFqQWp2iJjeERCcwkkI0M2IwhhKwgQk0KNoJRCCTQCMIJSB0SAJQQQQACEnCUiKByAggggAIIkaQAJLhqlIigABGiCNAAQQQSoAIII0ABBBBA0CCCCADSgiRpQAEoBEEsJyAXG3Kn01MZCAAokA1W26OqaKq2stME8YkifUN3mHg4DXHwViqKbK19nZFshQ7LXKWFssdvq3xkZDmwuIPtwidszchxt1Z/YP/AAXUb5tDcJaqQiqnYM4DWPLWgdwA4BVJvVyJ0ran+1d+KtOuPuZ8Mi6S3owJ2aufK3VuPCB/4KBLbKiKQtkp5muacEFhBC6U663InWtqf7V34qC9skr3OkLnucckkkkpjrRaqus/mME2hlz+af8A1Snm0UmPzb/6q2wpgeMYS20jf8mFG60XIWsyVNbZ5HBrIZCT3MJV5BsrcnY/5vq/7B34K5gp3RvDmbzSNchxWiobveJX7jK2pPeTM4AeJOUdkSWVti5joyDNk7lu5Nvqsf6F34J47Lz0jRLX080bOTSwjPmTw+a30d+q6cYjraiSTm90rvgM6KzsN5qq24R0ldI6op6g9VIyQ7wIOnNPVEfLRRu6tdH6YnJ6nRoY0BkbeDGjAChlW92h6mqnjHqse5oz4HCztXVtjJbEN+T4D2qaWoLZFV33vjlsfe9rGlzyA0cSSoE1wc/Ipm6f5R409g5qHM8yP3qh2+RwafVHsTfWvklEULHSSHg1gySqFuXr7TexeleHb5+A5HFx3pXGR/HLuSQZnPeGRhz5Dwa0ZJ9ivbdstU1JD7g8xN49WzV3tPALWWyx09G3FPC1neR6x8zxWTdnJPjlnV4fRJtba7I/5MTRbO3CrIM5FNGe/V3u5LQ2/ZWkgIc6IzP+1L2vhwWwpqBz3BrI3OcfqtGT7lpKDZapkZv1JZTxjiXnJx5clQnfZZ78GzXi4eIttbf5MXBb9ACNBwGFZ0VnmqCBBA6T9UfetLU1ezVkbmWT0uVviCPwVBdOkwtaY7ZTsjaOB3c/PT4JsKZT9hbeoaX0rS/Jc0myVU8B07ooG+J3iPd+KffQ2C36V1x614+qx33NyVy66bWXW4OPX1L908ic/Dh8FSS1Usp+kle7zOnuVyGDN+TLu6pH3lv+h1+fa7Zu3nFLRiR45uA+/JVbVdJ7wC2jpI428tCfwXLS/HA4STJ3K1Hp69zOs6rBeF/fk3lV0i3mX1JBGP0QB9yq6jbC7z5ElZJg/pO/FZbfPehvFWI4MF7FSXV5e3BdPvlfJ61Q5N/lSqJ1qH/BVId4o99SLEh8EL6tY/ct5q6oksl7Ekz3N9DxgnvljC1O19RLHspsxJE8szQwjIHLMgWGDs2C/Hupoh7541tdrmk7B7NO/wC5xf33/ipFSku0z7cycr1bsyTbjVf5Z3uCkxXisj9WocPcqkcEN4prxIP2L66rZ/5Gjg2qusB+jrJBjuc4fIqzpekG9QYzUOeO5xB+YWI3yhv+KilgwfsTx6tP3OoUvSfVDSpp4pB+rj5H7lZw7b2C4dm4W5jXHTI3T+BXHQ/xS2yHhnRVp9PXsWq+pxflf2O2Mptl7mAaWuNO92gD3YH+1+KZrNiZi3fpJoahnEa7vx1C49HUPjOY3uZ+qcK2tu0lyt7gaaqkb4BxCrTwZrwaFXUo+0mv68mkuezlRSkiop3x+JGnv4KhqrQRkhq1Nq6TKlrQy5QsnZzJbg+8fgtBT3HZe+Dj6HM7ifVGfMae/CqTolB8o0qs/a5W1+DjFds/G7LhHuO72aFU09pq6YkwnrG9x0K73cNjpHR9bQyR1UR1G6cH8D71kbhZZIXlksLo3dzhgpYX2V+4Tx8TK51p/g5O2csfuStc145OGCpEZG8HxOdG/wC004K19xsoe1zZIWuHjyWfqrHLES6lef1H/ir1Oam+eGZWV0SajuP1x/ySqK9zRANrGda3h1jB2vaFfU9RDUx78D2vb4cljIusbII5mOY/mCFZ0UBZIJYnGN/2hpn2LZpucvuOQzOmxjtw4fwaXdJT0Er4Q9vZfE8YfG8bzXjxCZoqjshtUA0/bHD2qxMAIyCCDzBCudikjBlZ6UtPhmeuWzMNaXS2fMU31qV7tD+oT8ishNSvikdHIxzJGnBa4YIPdhdNNOeIS6q30t0jDK8bsoGGVLfWb4O+0PiqluEn9UTVxesL7LfHycodD4FMvg8Ftbrs7Pb34kDXxH1JWHLXeX4KrfQa8veoVjs0p2wa2nwZl0PgU26HwWjfQ47vemXUXkpVjlCy6HyZ50XmkGLwK0BovJNmhPh71IqCrK+PyUPVIjEr00XkmzRHw96X9uR+vH5KUx6JBjwrt1H5e9MSUpwSACB4pjoaFV0WVBbhIIU2WLd4hRntwoJR0TRlsZKJLISComh4ESNEkACBQQQARCJKKSQgcEjRI8IFDRFBApBABGiRoACCCCUAwggggRgQQQSiBoAIJSQAIIIJyAUAlgJI4JbQnIB+Bbnoxdu7Z2c/58fIrDxLVbCVJpdqbZMBncmBx38VPU+Svkx3BmsrH787vNavYrZ6grqSuud5kmZbaIN3mxDtyOPBoP78Vi3v3pifFdH2Z/8ApntD/p4fuVibM6UXGCSHC/YUf4hd/wC2H4ohJsNyoLt/aj8VhpZDk6lJDz3lNaS92S148pe5vxJsN/1G7f2o/FOsdsQ7H8iuo/8AEH4rANeeZKtqGBscbaisJbEdWM4Ok/AePNN1vwyx+27VuTNrJsrabxQPq9nXVTTFkyU0wDnuaObDzWQqntazqom9XGD6vP295U6ivNVT1sVTTSmF8XqBvBo7sd3gtHerdBtPQvvFojEdfGM1dI3meb29/wC/Pi6MXB/UU7L2/oT4MATg+Cvtkjm/UGTxmbj3qjqGmM4xlys9i3bm01vzq4zNGvmp5NJCQolZHu9jGbVSPkr6ofm2da/zPaKyVVI2NuAMDgAO9ay7x1Fxu1THTM3sSu3nnRrRvHiVYWjZ2noyJHDr6j/KOHDyHJY+dlKvhvbO86N0mVkE4LS+THWzZ6rr3B9TvU8HIY7bvwW3tNlp6FgbTQhmeLuLj5lXFPRagBpJPAAcVpKCwbkXpFyeKaADJDiAfb3LBstna+fB2NVGPhR45f8AkpKG2vneI4Y3Od3DVaen2dipYuuus7IIhrug6+/8FWXDbOgtTHU1mhYXji8jPw/H3KZsXZqnbKSS4XieX0Jj+rZHG7DpXYyRnk0ZGcd6IUvW2U8vPcVuT0v8jVy2tttpY6K0U4dJw3yOP3n2rBX3aq5XFxEszms5N5D2cF3q5dGOz89GQ2gdSSEaTQSuLgfEOJB8lwLbCyTWK7z0NSWufGcte3hI06tcPAhX8eqtmLLqSkn2LX/JmqiZ8jy6RznO7ycqK56XNo4pgnK1YVJeDFyM2Tb2wy5ESi7/AAT1PSz1JxTwyS9+63IHtVmNfwjNsy9ctjWUXNXEGztdI3ekEcI/Tdr7gpVJYKaWthpPTjPVSu3WQU7Q5zj3DipfSfl8FN5sW9J7M8Ea7LZ+iOaUNdVU7IGn/rM+T/Vatbbui2w0Qc6vdG8t1xGwAe85KhnbVDzImhHIt+2DPNo1OBqfBXtvtFLDZnXe+SVEdK6Tq4YIABJM4cTk6NaO/BJXoX8i7I0ORHRRucBxc4/sVffKDZS6QRw1VDCGRnLQx2MKrPOqiuDRx+k5dr+paRwyCu2fno6qljopIYqgNbJv1DnPIa4OGvDiBwXVNndmodp7BRwTzsko4IxFFG9jmlrQcjtNIOc8ykVuzWzEcB/J1LEZe5wGPkpthpaOlwyd3VRDQNiduqrLqcN9qRqf9OzdfcpGO2g2EpYK+ahonTU9e1pdEx8nWRTYHqhxAc092cjK5xK10frtc39YYXpymGzUdYypfEJp2eq6V5dj2JyW2bJVxPWUFKC7mwlvyKsQ6hX7mbZ0jKh9qPLW8DwI96ML0jX9HGy9c1xp3SQkjTBa8e4hZm4dDUnV71FUUsvPdJdEfvCswyKp+5RsoyKvuicVQWt2j2RmsM7IbpHLRukz1fWOaWvx3O5qhltkjcmORjx7lOody2uSBZKT1Lgg5wjDkctPNH60bvMahNhNlX8liGS/Zjwd4p+KQtcC0kHvBUQJ6PiFBOlPyX6c2UWuTTWXaO4254NPUPx3b2M/cfaug2jbOluMTYbzSsfnTeDdfd+BXKqJhe4AAlxOAAOJ7l37ZHoxt0FJGbzD6ZXOAMjC9zY4ifqgNIJI5krLyaK48vg2odR1Hc+f+Smqtm6G4wma0VDHjmwn9yPasbdrBLTSlk0TmO5Z5+IPNdQ2r2HNppZK/Z50lNUQNL+oEjnNkaNSGk6g45agrI23bKCsYKa8wNc131wOPs+8Kj6DfK5NbD6k5L6Hv8e5j7dsm+83CKijYC6Q8TwaObvYug09osWyMQhobfFX1rfzlRVAOOfDkPIe9aTZS3UtO2urrfIJQ6Ldj1zu8+Pu4rOXaJ+8/eB3ueVtYslXDRz3VIf6he14SEnbYtG76BQtxy6tJ/js88KGiI/0ay9yo+tJzlrhwcFSStmp34kGRycOBWhCUJexzWX0eVXL5R0mHbDrB2aOizzBj1Cd/ja4f4nRf1FzMTEkHOHDgQpcNcSQ2Q4d396l7Yv2MizEdfK8HQf44E9l1HRlvMbiRV7SyNgM9Pb6CWEet9FhzfNYjfcU5T1MsEgfGSPDkUjrj7IKn28S8Ghdtu7lbrf/AGSQduHj/wC32/8AslQ11uZVxOqbcMPAzJTjiPFvh4LPSlw5lR7S4aLv7SMl3RZvjt08f/b6D+zSTt5J/wBQoP7Nc6e93eU26R32inpx+CCWGjpH8fZP+o0H9mh/H1/OhoP7Nc0L395RdY7vKXcfggeKdNG3W8daC3n/AMJIqJtl9qR1F8tUEEjtG1VMNxzD35H35C5qJXA+sVNoah3WDUpUosjlS4cpmX6RdkJ9lL06klcJaeRvWU84GBIzv8COBH4rDTswvQnSVE25dFNtrZsOqKKr6prue44EY+DfcuBVLQCcKCyO0aOJa5x5K88Ugp141SCFTZfQnkiKPCJMYoSCCCACKBRoIFTEoIEIkCikRQCB4JABnRBDCCUA0aII0AwIIIIGgRhAIwMIANBBBKgAEY4oJQCUABOBJAS2hOHJD0Sv9l3bl7ond0gKoYwrzZ4YutL+uFJB8jbY7izWA5lXTNmv/pntD/p4fmFzRo+lXTNmh/8ADXaEf56H5hTyZn3Q+lGGlGpSWtwn5G9oq3oqKOjgZWVjN6RwzBCef6Th3dw5ps229I0K4qMe5iKKjjpIW1Vczec4ZigPP9J3h3DmmqieSeZ0krsuKFRLJPM6SZxc9xySUlrcqeEO0zcnIdz0vAuJ2qvtm7lPQXGKopHbr2nBzwI5g94Wea0u9U4YOfeptHIWysa0Z1GiWUlrQ2vGcl3SND0nUsFFtFUtp42xMe1kpDdBlwyfiq/YW2TSX6hqZwY4myhzRjV34BbDbqgjn2lFRMA76CLdZjQEDiUVgjH5Ups8d8LOnkNJRR1fT+mqWP6lvj2RiZ6RkVRM2FjWM6x2g8yrG0Wmavf9C3djBw6R3AfiVbvs8cTpau5vEUAcSGnQnU8fw4rIbVbeFkbqKzNEUYG6XDQ+Xh5BYtkHbN6OzWSq6VGHCSNVdLxZtlYSIiKmtxguJ4H9+QXMNodq668TOMkrmRcmA4x+Cz1RVSTyF8ri9x5kpgvV2jCUeZGJk9R7dqL/ANyxppNeK790NXOF2yzIWkdbSVD+sHPD8FrvmPYvOcUhBV5ZL7WWeoFTQVDoJgMEt1BHcQdCPAqW/GdkHFGY8pT+5nryrvDDTFowdMZXnXpmr46zajcjILqeBkMmPt5LiPZvAKZPtNeqmjrW0VUGzi5S07XBoG5E1jSMHvy7jxWWq4bdRZdcak1FRxMbe/x5+8pmHhWRl3TZVvyaKVqvlmSEE1TIWwROkPPA0HtU2GydW3rLhVR08fgRn3nT5pytvshaY6KJlPHywMn8AqKd8k0m/K50jj9ZxyVtRUIfkw7Z22vfhGgbV2KiP0NO+slH1n8M+3T4KTQ3O83qrbRWSj3pXcGQs3nAd5J0A8TgJvYXY2s2oqi8E01tjdiaqLc6/ZYPrO+A5rtMUlm2Ntfo1uhZCzGXHOXynve7n8gnO6XiJVdME9y5MxZei/ea2o2wucsr+PotPJho8HP5/wBEe1W9dLs7sqyiqbNQ0dOaOrhkmdG3L3RF24/LjqcB+ePJZa+7X1VxldFTktZnAAKr47fJXUlTHUPcX1EL4uOdXA4+OFDNSafcyxQlGaeuDpN02nrn1MsNMCNxxYT34OMqunr68iL0qUgTOMOc8CRlvxb8VG2arGXGzUVaQOsngjkf+tugO/2gVOucLa63y0+/1ZcMseOLXA5B965WyUu57Z6tTCr049kRUVqfId6aUkqbHZ4OYys5T7VSW5ogv9JPDI3T0iKMvik8QRw8iprdtbLgfy3HnG/8FG3H3JJK1/aXzLZTjhGPcjdboD9UKkG2dmPCsP8AZv8AwRjbGzn/AB0f2b/wSbiRdl35LKS1QnkokloGfo3EJobW2Z5wLhED4tcPuUiDaC0zOG5WiUn6sMb5HHywEaTF9SyC2xiFs1JMGNkO+85AzybqfuUqLaG40zsOfvDxT1HSyVFRLWywvia8bkMT/WazmXDkSeXIIVtvJjeQ3gD8kaklwwU6rH9aEXHaG23K8U1FeYIJ4IqJsj2TMD29ZK8kcee6z4qou/RvYLsx09hqX2yc6gROL4j5sJyPYfYsTMJLjcbzWRklhrDBGR9iJjYx8Q5PUF3rrZMNyR2AeC6nFg/Si98nmvU9fuJKPjZn9pbBftl5d25QiSmJwypZ2o3e3iD4FUpnjl/ORgHmQu/bP7R0t4pjTXFsbxINxzXgEEdxB4rD9IPRz6BHJc7AHPpAC6SmGpjHezvaO7iPFWVY1xIoJI5v1Mbh9FJr3FBrXMPaCjE66HVPRSuB70rSZYrk4vyX1hnZS3KjqJBlkUzJHDvDXAn5L1ZablEx7n77XRSfSMeDo5p1BHhheRaaZo5YWstO1t0t9rmgpqsiGMMMbXNDtzMjQd3PAYJ04LJzsWViTj7G1j2wktTPRt/vlPBR1FTK8CCnidI8+AGg9pwF5dleHEZHHktB0hX2umvNVbpKh/oUEg3IRoCe8957srItlyQlwsaUF9XuT+vCpfQde6LquSPZy/P3i4xBhb3jQq1irqW5t6qpw2UfWGiznRrJjZTaX9VnyKrpKhzHuc1xDhkgjkrtmOpb0ZuP1OULpN8o1lXs7VvBMNPLOz7TGEqmqtmri4Ob+TqpzTxHUldYN6paT8nWyWY00lTTNMUmgaDoMeB+apb5UX6kmcIax+n1Nxuo7wcfBU4ycfJoVZs8luMUv9zk9TsjeI3ZhttaWd3UuJCQ3Ze9OGDaa7H+gd+C3Um0t9adbhIMfoN/BQ6nazaID6G5SZHLq2a/BW43TfjRn5PTrVuaRm4NnL3H2XWquLP9C7ITdZQT0km5UwywyYzuyNLTjyK6Psrcr/U0rrrfbo+ltEOuXsYDLju0zjPPieSa2/uUN42Ntl1giLWPqXMbv+sG9of+nOFJG+XcotGBOpc68nNoZXwyB8bi1w4EIXOhZcY3VNIxraoDMkQ03/Fvj4Ky2etEt8ukFHTODesJJeRkNaOJ/fmuiO2c2RtNTBQ1tS4VrwCC+ZzXa8Cd3RuvDKffZCL0/I/FslD+hwN8RJI5pswkrsm1GwlHSX6iqHvIt08oE+Tg4HrajnjmOKt7VshsNdJZY7c99RJE0Oe1lS/LQTjJyof3EEtl2xe6OBOgKQ6ErtO0Vl2DoKa4U7J9y5Qse1sRneSJANBjhxwn9n9i9mZdjKK7XeKVm9TiWeUzPaBrxwE/14a3plR7bOFOjIUiiaRIO/K7TJ0f7K3+gnds1WubPGcbwlMjQ7kHNdqAe8Lkc1LJQ10tPO3dmheY3t7nA4KlqnGb4IbN6NDtf/8ARk//AJBnzK4FWDUrv213/wBG/wD/ACLPvXBKwalE/tY7CfDKuQapsp1/FNlUJGohvmglHgkJg4NJSkRCQAkEeiCACSTxSkRCByEo0SCQAwjQQCUA0EEECMCCCASiBgJSCCQAI0SMapwBgJSIJQQKkKAyptPQVM8LpYonujbxcG6BQ2DgtlYtp226yzURgD3Ozg+aZZJpcIu4lVc5fxHozEYIOO5Xmzw/50pf1wqj15HOxjJVzs+3/nSm/XCkrfKG2wSi9Gtaz6VdJ2bYR0cbQAjjNCfkueRNzKuq7GMi/iLepKxp9GE0RI+1jGnvwrLkZ1lX0oydqthMkE0kLp5ZnYpaYDWV32j+iPHu7laXHZi/ETVlXFTnA3nEVAJx5YUnZO4xv2udU1ssULPR5AzfcGhurcAZ04ZWzvN1t8lqq2MrqRz3R4DRM3JORpxWLn9QuxruyCL9dFeRDnwYOfYy808Ek0sEG5GMuxUNPPCcqdir1TQySywQCONpc/dqGk4C6Rf34s9w/UP94KZtA8CzXFznANELySTgBUl1vIY5dNpXOjl9ZsVfYIXvNHG4MGd2KZr3accDmm7HbmwOZK8tfKTkEagA934rrX5XtnWH/nGjzvcpm9/msHTQiesn9Gw6M1Mu4W8N3fOMHuVvE6hbe3GZfxcetNvXsXG1zHOvTQ0FzjEwADnonrJFBQ1tM6oeOve8Bre79+9L2xr4LVUmZ+HVDo2geWNFgLZdZqvaaifM4kde3A9quwqlbLjwWpZUaMXT+DPbfbSVFyrZoWSFsDHuaANMjJXPp3alWt5qN+smy767uJ8VTSHeOmvkrkcdQ8FG7qLnFcjLnIg5Bw0R03VCpiNQCYA4b4BwcKaMTJtvb5JdDST1km5TsLjzPADzKuzSUNpj366Tr58ZETdfh95SLzXzW/q6eia2GF7ctewcfLu81QbxeXOJJc45JOpJU7jGHHuZ6ssu5b0jWXOpfHabm6N7mH8rzNy04OC1mRkLKmU5OvFai405no7pEHbgF2nJPkI1SCWjo3Yib10g5/t/BRRhvyTyu7eEuRNPQVFQAQ3dafrO0Wg2T2RN+vDaMS4ijHWVErf5tnl3ngP2LOvuFTO7d3iwHQNZxPh4rvOxtids9s9HRMYPT5wJ61/2SeDM/ojTzylskoR+nyR1qVk13vSHblUU1jtjKeiibT0tO3dijbyH3nvPNcg2ivUldVOc9xLc8Atb0h3Lq8w57Q7lymecl5OTxUdHd27kWciFSlqvwaa21DGEOPFXsV0ZHh7Tq3te5c5kujYNDJr3Kvm2qZESAc+Z/BPlKK8kcYN+DrmyVd6H6dQE9mnqZWs/Uc7rG/B6vn3M8iuEW7bZzLm6V5axr42MJA5sG6CR4twPYtF/HiPd1fB7AVymXVNWPtXB6n0fMxrMWPqSSklpnUhdHj1XEZ7jhKbcXn6y5M7btjeD4iP1SkHpBDfVcz+qqvpW/BoyysFeZo7JFcHfbVhS1QkIyVwr/lFeOD2D+inI+kuZpG7IAfBqdGm34K88rCfCmj0ZSQwyY3mtJVvBSxNAw3C83UvS1XREbs0eP0o1cU3TZcGjBFG/9aM/crEYSXlGZd2y+yxf3PQLYm9yh7QSRUNhr6p+AIoXOyfJcag6cpW462loXeTntVHt90vTXrZyooIo4IWTjq3GIucfaTyUig29aKVqdcXNyWl+Tp3RxYopNh7bLUtzLUMdUOJ73uLvvT942ObI0ugAzxwue7L9O1uo6Okoa2zSNhgiZEH01QCcNAGd1wHd3rqWzfSLsrtC5kVHdI4al/Cnqx1Lj4Ansn2FbcZSguDiLk5ycn7nOqmjqLXV53S0tK3uzF7fV0rYy/L29/JTtrbIyphe4NxJjK5zbKiW03QAnTewfFT7dkdryMpUIzXf4IvSlsi2heb1a4t2kldioiaNInn6w7mk8uR81z1o1XpSmfHcKYioiElDOwxzMOoIOi4PtVaJdmNpKihfh4geHxOdqJGHVp93xBTqLHL6ZeRcmCrk/Te0VGSw4III0PgVJhmPo84zxMQ//itVibpQXPs3KHqpeUo/HiPblRq21mkYyWKZstNLNE1p5+uD5FTWV8bRBTkPfbJaZbbfyf4V1viR96oo5NQrbpAIG09X4k/3nKgidqlqj4HSuetHW+jZ/wDgftMfCMfAqomkJLjnkVN6OHH+J+0v/h/Iqud67vapXHmRlwsfqSN/0nZE1l/1MfcrLYvaZteyGz3jekLiGU9QBlzXcmu7/P396idJUD56yxRQsc+V9KGtY0ZJORoE6w02wduD5Orn2iqGdlvFsDT+/t8lnNRlWl7mhVfKHKLW/wBkMUp61oa4+rIBo9RbbYKemhdcr0Nyii1bHjJkPLTu+aorJt/WUUD4LlELlC5xe3rXYc12c8cHIzy5cldWnbN9yq3mra3qnjcdTcWFvhnn81C6bK/Pg3as2zJj6a8ma2yu9Tf5WsLjDSRH6KAHQeJ7z8uSl3zei6JbG12jhUuz73qw2k2fZAwVtuJkoJPaYj3HwTe0dNv9G9pj4YqHH4vU0ZrUV7bIMrErnqVS58DfQo0OvNyedS2naB4Zdr8lUbdyuftZdi4klspaPINACm9EFdHQbUy0lS4NNXD1bCeBeDkD26qz2z2Nu1ZtNUz2+AS01W4P6zfAEZIwd7PDhlP7krm5fBi3VOMe3XuaTbiQnYOlqC49az0eQO55IA+9VfRa+GouVyqIwGSPhYJGjv3jqnelKsiotmaS1h+ZpCzDe5jBx9+FU9DjsXS5H/u7f7yijD+A5ArmrOz2ZhtvWkbZXnxqn/curWqinufRPTUVKGmeaiDWB7sAne71z/pEt4O0Nyq4cujNQ4SD7D/wK3EVTUUHQ5HU0cr4aiKhDmSM0LTvcQnWS3CGiSVXY+fcc6Ptl63Z59wrLrJBGJYw3cZJkNa0klzjwH/uuLbS1kdx2nuVZT/mZ6h72eLc6FLum1F5uMDoK+6Vc8JOsbpDunzA4qohfvSDIViqElJyk+WQThqOkaja7XoaH/5Bv3rgtaNSu+bXf/Rpv/5BvzK4JW+sU6f2sTCXkq5OKaKek4pohUJGokIKSlEIk0UIIIFAFIwElBGUSQAIIIIBCSiSiiSDwwjRBGlEYEEEEo0CUEQSkgAQCCATgDRhAcUrCA0AJQRAJbRlKh6QtgUiMJDGFSY2JkixXHY5CzOFebPs/wCdaX9cKsp2E8QFp9kaCSt2gt9PCMySSBrRyRX9xasj/DaNTYbe+41/Vt7ETO1LJ9hv49y6PT1sU+w19hpBu00D4Y2Y56jJWQuzo7PSfkqlcDK471RKOLnd3l93mrnZ8/4A3/H+Vh+YV6Fe/rZgdRyVGKqh/uK6OBv7SP0zimfyz9Zi6LcafraCqZJDvMdC8FpbkEbp4rmGwUFPVbQPiqomysFO9267hnebqt/PZraaabdoYC7q34wDx3T4rmOtJfujW6Z/2EHSWptTaoI5q+5OZJAwPBqBr2Rz3cp+vowG03XVNbUt9Lg+jml32Htji0AZ79Uq3V9I63UhbWUx+hYPzzPsjxTN2no6ynipzNTzb9TDmNsgJcN8cgcrHW+40ODTxuecHdd54Kw89xhtwqw0fyl9RNnPL6RyvGWm2hw/kcXvP4rl9fKGXasiZoyOoka1vcA86LW6PX6ljQy2/wDbwcjRdJzZajaJrG64p4zx0GQqPZ23Rx3ake/MjxKDxwArjpFrHU20ZcGhwNLFp47qzFj9MrrzSydpzGSgnk1q66iKUUcvfkTnDlkGS4WWkne2R1Ex2TloYHHj4AqVTTbL3N3Vyfk6Rx5OHVuPkdCoUPR+yZ7pKu4Sb7yXbsMYwPaU3W9Gwcw+hXBxfyZUR6H2j8FZ5+ChKytpfUx+9dHdPUMMtlndBJxEMx3mO8ncR8QudXK3VNuqn0tfA+GdvFjhxHeDzHiFqoKzaHYmqZFVNc6lcdInuLopBz3Hcj++F0E09q27sDHua5pHqvIxJTv7vL4EJrgmCyJ1eXuJyekYbpZXUzgTUUx+iceY5Nz8Pcqy31JpKuGoa0OdC8P3XcDgq32iNZZq2W19X6MYjgub9cHg4HuI9qz5GiZPS8FunlN+zNTe5M014af+1ag8e8RrMNaMq5u8p9JvEZ/7RnP9xVsML5ZGtjY57zwa0Ek+wKNeCy01rRqeiy1NuW1kU07d6loGGqkzzI0YP62D7F3WpnNFa5JZz9JLl78rFdDtinpLZVPq4JYZqupaC2Rha7q4254HkS5WfSbcBS0D4w7iOSif1S0iJ73ycd2wuZqrjMd7IysFdbkIQQ1xyeGOJVldakySy5OgBc49wCyrc1E7p3jj6oPIJbJaWkWqorW2I6uaqOZXFrD9UKXT0cTOETSf0hlSImaKXFCXHRRKMV5LCTfgZAJYWbrQw8QGjHySBRw5z1bR7FZspHEInQEexOXY/IrhZHwQWUkP+TCeZRwc42+5PBmEtuikVcH7EMpzXlhQ0VOT+ZafYrKioaQOG/TxO8wFGiKnQOxgJ3ZH4IJWS+TcbMW2w1BayqtVG495j4rbxbG7MPaCbHQH+h+1cutdUYpGkaYXUdnLj6TTgOPaCisgvKCNsvGx1uwuyxIP5Cof6p/FXVDY7ZRQOho7dRwwu1LGwtwfPRPQuyApTVA+CTcn7mfuewmzN0afTbJRFx+vGzq3e9uFznavoTiZFJUbK1skcg1FJUuDmu8A78feu1b2ElzsoTE24nnLY7pDvuxNz/Iu0sNRNQsduPppTl8PjET7906HlhdC2lbT1EVPcbfM2ejqWCSKZnB7e/wPIjkQl9MWx8O0VjfVQRgXKkaXxvaNXMHFp+5c86Irw+poa/ZqreXHDqqlDj6srRmRo/Wbrjvb4qSt6Yskpra8nZujy6NmgNLKc8lSdNVq6200tza3M1FJ6NKe+J2rD7Dp7VTbL1porq3LsAngunbTUTbxYaqADeFZTPiH64G8w+8J8l2z7iFPfB5qAypdM9wbHHvHdNREd3OnrBCeiqaQMFXTTU7ncBLG5mfLICbaMTweErD/ALTVNJrt4FhF92mbPayOhqb5VU9U7q6jrHlkg0Pru08fJZSrt9RQy/StzHnSQcD+CsNvXb201XnhvO0/puUW13WSACGoHX0503XakDu14+RVitppJlK2M4Nyi9/g6F0bjOx+0nnH8iq+TR558Vpej6lp5dmdoGW873WtY8MzqMA8FnKlp3iQneXJFCEl3ts7tSS09xtdNcrS+jfcBTCGGSd2kXDeBA1Bz+HBYis2Cu1ZUSVFVdbdJNId57nSEkn3LnBcRnxSC4kqnHGlB7iy8ppo6Cejm450uFt/tD+Ceg6PbpE8OZX27I5iQ/guds3uaeY5w4ZTnXZ8/wCCaq1xe0zumztpuNCCyqnoponjdkZv5Dh7RxUHb6mpqSw0dBTEYbM57W5zgYPwydFyOnqpInAteWkc8raWa7xXOiNFWevwa7mDy/f2KjdTKv6vJ0GDNZFilJ8ox1fC5r+ySx7TlrhoQe9ToukXaWmjMDq5rnN0DpYWud555+am3a3PjmdHINRwcODgszcbeZGjHrt4E/JLVZGXE0X+o9PjdH1IeRupu1TX1rp7hUPnlk4yPOT5eAV1YL9W2KWWS3SMY+Voa4uYHaA55rJCNw7Lhgg4IUyklcR1b+I4HvV9JSj2+xx99TrfcjSwXd81wqJa7EratxMwxgEnjpySNob1eKK0/kdtXvWd8e5EOrbkszndLsZyqY5VjRhlfTOt9U7G9rG8/VcmWVJfUl4J8S9S/hT/ANjGS5JKcpB2wpVdQyUlQ+GZu69pwQk0sPayiD2SXx7U0aba4f8AwbaP/wBwZ8yuCVnErve37hR9EtDDJ2X1Va17AeJADifu964JWcSm2PSZDgw2mysk4pop+QJkjiqbZo60NlElFJTNjGguKIo0ECCURRoFIKJKNAokAGklK4oigcgwggEaBGEggjwlEDCNBBAACNBGAgAwl4RN1KcDCnJCoSAn4WZKQ1pT8eiTeiWMdnStlujaqvWylTe4poWxQBx3XHV2Bk4WImh6qUt7ip9u2huNLb5aGGrmZSS+vG15DXeYUQnrH7xTrZwceCbDptU25vgcpW8M58V2Lo1tUdqdQ3KsH8rq5BHAw8WtPPzPHy81hOj+yOu92zKP5BTgSTk8HDkz2ke4FbKivJu231sMJ/ksE4ZGBwPHJ9vywkx4epLRY6jcsWhyfl+CNcS6Ssle85e5xJPitVYARsHf/wDSw/MLL1WtQ8/pH5rY7PNB2C2gI5SQ/NatrUYrRxcE7NbKzYWAybRPaJponejvOYX7p9ZunA6LcXSlfHbKl3p9ecM4GYYIyAQcNHJc8sJrKW6iso93MYIcHglrweLdP3GAtbW32qqqOaD8nxt6xuN70nQa5+yuV6pjW2X98OTtcGhqpJI0d8paZlnrGspoGsazdAEbdACMcke0lHTvtNWRDG1zBvscxga5jgRhzSNQR3qquF1q57VUmWgihjkb6zqnhrnhuqBc9sjVUtRALbu9aMBxqAca/qrPhgXz8IltkqvvNU6hkEhAuFwxk/zrf+Fckri6O+V7S9z92pkG87ie2dStfVbfSFjzBbA2Q53XPnyGnxAbqsIHPknc+RxdI9xe5x4kk5J+K2ukYVtEpSsWjJz8mEoaizV9KDs7Rj/Vof7qj7MXOI1dDB1R398N00b5pXSef8JT4U0P91Uuymt+oAOczVv1rUEc+5d1ZQ1T9qL5LI6i9NdAHEN6k9XGNe/TPvTLKra/Z1zHzit6kuxu1H0sbj3Zyce8LUz7csZ1NLQW10kzRuua94axuNNMZOPcrezbVUNfWsttZG2CpmGA3O9G8/ZOeBPceKm1xsglZJLTjwO2K623aqikt1xgiFVub0tKTn+mw+HvCw87q7YTbFpke6aikGRpgTQk66fab8x3FDbizTbIbQUl4tBMcEkhcwco5BqWeLSOHhkcla9IV+st72SpZaeqidX9YySOEH6SPOj2uHLT4gJrYyuPK7eYv/BP6VrVBcNnYrxTlrn0265sg4SRPI08dSCPauQkae1SZbjWS0UdI+qndSRneZAXksafAK/sGzUdXbm3K61D6aie8xwxxtzLO5vrbudA0cCSopteTRx6nVHtb2QJKGa7bY1drpSeuqLnO0YGcDsZPuBXYLFOLG0UVkt8FM1h3Xy729JIeZc7iT8FjLBSxUm3sN1hp5IzIKyoLnyb3a6lx0HJWNvvQbNACMEuaM571g9SvlGSjFnoP6awa76pWSjto3/R5dpbw24VE7t58E0jCfEuz8lz7pgrC6dzASAOSsOg+67820tI4jIqTKNfYsj0q1O/cZW5zhaGLzFNnJ9QillTS+Tld0cRbppPrVEohaf0RqfmFWRDkFY3okU1qi/zT5j/AEnFQIRqpJvkILgsKSPeIC1uzOztbe66Kkt1M+eeTg0cMcyTyA7yqC1RF72tA1K9g9DGysNh2ZgqXxg1tY0SyPI1DT6rfIDXzKzcvJdfCNiiuFVfqSWzn9s6Cqt9M019ziieR6kMJfj2kjPuWb2x6IbvZKaSqpnsuFKwZeY2lr2DvLdcjyK9U7uEiWMOYRhZkcixPexyym+JJaPBFXT9XnRQiCCuqdOGz8di2sl9FjDKSrb17GgaNOcOA9uvtXK5T2it/Ev9SCbKWbQovcfDFscpkL+GpVa12qlxOwr2zJaLukkw5ozot1snUOEzW50PJc7pH5IK3myO++qY2AAykYjB4b5OG/EhQXz7Y7J8ej1JaOnW+KuuNS+kslM2oqI8ddNK7dhgzycRq536I9uFe/xI2hLN836lbL/k20I3PLV2fitrs1aILJaKeiphkRt7bzxkedXOPiTkq0OM6rn55E5PezTTjDiCOMXCouViqoqfaSljiikduR11OSYXOPAOB1YT46Kc4kLpV6tlLdrZUUVbEJKeZhY9p7vDxXHrJJNSsq7VWvMlXbJ3Urnu4yMABY4+bSPcreLe5PtkRZFUZw74rTXkm1ZBieDrlpXmOvkOzPSJDW04xEycTADgQD2h7i4L0nWyhsMjjwAJXm3pFPWVMU32JcadxWlFfTszIv6tG/uQFFe544z2GSENP6Ocj4YXXrNXZ2VFQMF8IDxkZ4LiFRUmqit9STl01FA8nvIYGk+9q6bYa3d2FqiSfU3R7Sn3fZsdjx3dFfkm0t+qq/Z+lZXNjq6aSIB8U7A9hxpwK5lt7Y47TW22sooHQ0NbJlrN7eaxzXNy1p441zrw1XU+jKmZctjaYuAduuc3XzVNt5RMFNRUUtP6SymrXyMjJPAxbw4HOmCsLEssjbpvhnadTox5VPtjqUTme3OTtNV6cXO/vuVNEcHxW8utoptoZZJaRzqa64cfR5Dlkx1OGni12p45HAaLBaArp65I4C1aNpsBtGdnrw2oe0yUzx1c8Y4uYe7xHELptz2epr5Ga/Z6ohqYX9ota7BB7iORXB4Zd1bbYaxXG6yirjmmo6JpwZmOLXSEcm9/mdArEo7+uL0zKyIqK7mXtVszcoGudJSPwO7B+SKm2ZrZSN6NsQP23fcF06wtLBKySSR0UcR1kcXHzJKy1TtFA127SwulP2ndlv4pIWSm3HXgoq6ek0VkWyMmNaiPPg0lPjYqve3egYyVveDu/NaajqDQ21102hfFSUo9SENO+8/PJ7lQf8qlMap0clBLDStOGGJ4LgO8jT4FROc5Nqtb0Twss1tkN+xt2adaR3sIKdh2Tu8Tw9lM4OH6Q/FbK2Xeiv8ARvdRVfXxkYe0PLXNz3ji1YLbi03yyxSV9uudwmt7TmRpmcXw+J11b48ufeonJy4lpF7EyrI2JJ6ZuqOx1dfQCO4QFkrfVfkE/v8ANVNVsbcHZDacnGmQQuTUu2N3ppmu/KdY5oOrTO7Ue/iujU97m2gsomoq2dtbE3tNbI4b3szz+B0WZcvRlv2O8xFkZMN9y2RbhsJdHO346R+e4Ea/FV8mw950IopA4HQhzfxVPcbxdmgltyrWkf55w+9ZS47S3qCXeF0rww8R6Q/Q+9T0ZSb7Uyl1HoeT2u3a17nTWbH3cgb1FID5j8VJg2OuzXB3ojwRz3h+K5VTbYXeCWOV10rnR5w9pqHHI7+K0zdpLi9oc25VZYRkETu/FXtymuGjlLcWyiemb277I1txpI5HUjm1ceh1HaCrYdkW25pqr7PDR0bO050jwN7wWetW1dfT1rDPW1MkROHB0rj96zvSfST09wirmTSzUVZ2mF7y7q34yW68O8e3uVeU3S9M1KMazNhvfjyQ+lHauPaG4wxUIcy2UbTHTtIwXE8Xkcs4AA5ALm1Qc5VlVOJJyVVzc1Vsu2aNeKqY9qIcgTBHFSXjVMuHFRqQycdDJREJZSSnELQghEEohJSDAiMII8IkgoRRJSSlAARFGgkFQfBEjRJRAJQRDilIACMIkaUAJQ0RBK4oAdgbl4HeuwbJdF35c2NqLw2rjY+IOLYzzwM6nkuPMOCFpbdtVc6K3SUVPVyMppB24wdCp6pRXkgyKrJ69NlfX03o1Q+PuKjtalyTOmeXO1JS4254KvbJN8GnjwekmKiap9HC+eZkUTC+R7g1rQMkknAAUdsRaMkHC6D0XWtjZp77WDdp6MEROdw38ZLv6I+JVWW/BsY8E+S5vYZsnsrBZ6Zw9PqQXTvb/tEeHBo9qr+jxn+Etsx/lx8ln7xc5L1d5at+e27dY0/VbyCv9jquK2X6hnqdGQztL8akDOq28Wn0q/ycl1jJeTY9eF4LGqBNS9uvrH5rT7IXqGjNRb6umdU0Fa0MkjYcOBHBw8kxc9nqkTySUb4KiGQlzZGStw5pOnEp+y2OrpQ6WeEiR+g1Bw39qbkT1Ek6TiQv1CX+5r4G7MRsDIoK0N8T+1TaOjsUuZmxVIYw5y86Kio7fNLOxmC3eOp7gnNq68UFI2hpeycdo5Hu+9Zm5TlpHVyx66I8Tel+Rd6u+zMr+pqBcMMPCPAGfeqkVWxh0Iuw/qrHzQyvc7dG8f1h+KZNDVnGIXHyI/FaldOlo5HNuVk2+96Nk6bYw87sPLdSWz7GQOErY7rOW6iN+6A7wKyUVqr5HDFO7H6w/FSPyJcSNKd2P1h+KmVf5ZkzlHx3A2jvEl5us9ZK1rN/AawcGNAwAj2Sa47Q0G6M4maT4DKDNnri4geiuJPAbw/FaC02z8gyMra8shhh+ke9zhrjkBxJUvbpaIJ2qMe2Jh6WGN12Fvgdu1Eznb8nEtxk+/uCG1+ywstFDcKWoleOsAkDz2muOocCPELM1FZLFX+lU8jo5myGRrxxac5Ui+bTXK9U8UFdLH1MZ3gyNgYC7vPeUOfsWI0WbTT49x7aXau6bQUlPTXCSIxQu3huRhpe7GN5x5n3cVnmtLnbrQST3JcbHSv3WjU/BSnvZTMLI9ZObkzWy0koLtihtu5TYL8Pk5BafaW6Otdo2UhZjP5M645+0+V5PyCx7tXZOSSpvSRNiTZxgOjbLTjHtcobX4Jqo8l5s5fJa664c783RVrv/wCDj70mCpIqYDng9vzCy+wlRi81Iz/9uq/iwK1EhEjTngQVzXVObUenfpJ9uLP+po+hKs3Nr73GTo8yHCqOkmffr6k54byT0NSO/jtWkH1hKoW32TW1XM9orcxF/CicD1J7y5/1MltGNyvpWfYoYB725+9QIuKsdqR/zy3xo6cj+oFWMOClkttjIvRqNmiDcKZruDpGj4r19tP0gWjZGxUoaRU1r4m9VTRuAIGOLj9UfFeJ6aoLCCHYIU+W6SzPL5pXyPOpc4kk+ZWdfi+pLZrV3QlFKfsdwrumnaGaZzoJaenYToyOMYHtOSrvZjpvn9IZDfYYpInHBlZhpH3e/wB4XnH00nmlNqnHgdU39mtEsr6Xwonb/wCEPfLddZ7Q+3zsmIie5wGjm5I0I5HTguHSO7ZTsk0koHWPc4AYblxOB3DuUctJKt41SqWipk2d6UV7ADk/E5MBhTzGkK8pIzXWyypZMOC6F0bVUUd8pnyuG7G9kh8A14J+GvsXNY8ghWlBVy0srZIJHxvbqHNOCPaoroKyLiWMeTrlto9Q7QdJ9HS1LqSz9XUuYcPqM5YD3N+158PNVVP0j1JkzI4kfolvywuAi5Pc8ukeS5xySTxUuG5kY7SpwwYpaLE7orwj1BZduKSt7E72jveBjd/WHd4j24WDu00TtudpZoXtMO/TxlzTkF4j7WvkQuV0V7lppmSwyuY9pyHA6qVW7UTz6ySDvO60NGeegSwweyxSRBLKioOOvJqdpLuyKlla1+pGOK4Vti/raKU5yQ4H4rVXa5Gdp7WQfFYvaCTeoJ/Z81f7O2LM+PMka+gdv7PWR45Uz2e6V/4rbW6tLNkZWk6GQZ9gKwVrJ/izZx3Ry/7wrQGZ0ezLteMmPgksW6yzif8AuI/1OpdBFQH7GtyeErviAVaXwM/jtamv4STge+Cb8Fz7ofv0Vt2cEcj8bzw74K22n2hjbdaG6B2Yqeqhz7WSj71zdM07FH32dv1DFmqp264aNltFaaNkEdxjiYyopZopQ4DGgkbke7K887Swtpdo7rAwYZFVzMA8A84XUbp0gU1VQS0rXAvm3Y8Z5lwXM9uznba/YOnp0398rpKFKL5PPLefBVMd2gup7Nbf0VDs1T0k9LKaumjETGMADJAOBJ5eOi5MwnKkRPI0V+GnxIz8iiNq5O6dGV0q75dL3NUv33mkDWMGjW5J0A+9aaybM0toDKu5ET1Whji5M8fE+PBcx6J9qLdYpK5twlFO6drdyZwJbgZ7Jxw45Tm1XSVPVTvishdHFwNQ9vbf+qD6o+Pkop1zlY1HhMzpQaeoo6LfLPSX6cTXOJ8paN1gEjg1g8ADj2rI3ro3ppo3SWirkhm1xHP22HwzxHxXOn3y9PHpP5RrwM/nBK8N9/BaLZjpJraOobDfXOq6UkAyhv0sfjp6w+Kl7JVr6WNjVbH6ovZmpX3jZW+DeM1FXRagjg5vhyc0+5dAr+lemqtlpoXUTxdponQvbgdSMjBfnjj9HHHmqTpY2ns96p6Gmtb21UsTzI6oDSA1pGN0EjXXU+QXNpRJE7dla5jsZwQRpyUU9TW5eTUorViUprTHnSngM6K62VvctpuUUjHnqycFpOnt8/2rNBxJUiIqhdWpppnX9PyvTkmjsO0FDDV0rLnRawzfnB9l3/voVz27UQG+HN7LtMLT9Hd+YxzrbXOBp5hu9o6A8M/cfYVJ2ltBpqiSPGW8WnvCwZqVM9Hc4tsLI88pnIpA6mnMTzpyPeFc2GtIJpHuOnajJ7uYRbQW4lpcxp6xvq+I5hUUL3ODXx5EkZ3mnxWvi5G9bOR630xQbUf6o2pJPPK1lmbDtFZKmyV5G85uYnniwjUEeR+9YyimbU0zJWaBw1HceasrbVvoayKeM4LDlXL6/Vho5rCyHjWqXt7mBu9HNQ1s9LVM3JoXljx4j7lUShdd6WrUyupaTaGibo9rYqgD/Zd7PV9y5RIzisZN+GdTdBNd0fDIDmppzVZUsMUlXCyeTqoXPaHyYzujOpVhtnbrVbb1JT2Ku9PomsaRN3uxqFZjHa2ZFskp9hl3BIKfe1NEJxBIQUg8U4UkhLoiYlERlL3UW6k0AjCIpbgkoASggUEmgAggjCUAwjQQQgAEaJGEoBpQSQlNQKhbRqn2BMsUmPkkkyeEdj0UZdwBKlws3TqFp+jetslDeWy7SUpqaLdILAM9rkcKuvstHPdqiW3RmKldI4xsOpa3OgTZRSj3bLVEm7HDXBbzXB17tVmstJb6aOqgeY2zRtw+YuOm95LU7dyxWDZ2h2doXZLmb0rhxLQckn9Z2fYFG6KLW0zVN4qsNipwY4yeTiO072N+azu0ta+7Xeor3+rK76Nv2WDRo93zTsWLus7n4RYz5xw8bsh5kVcbt1w8Fsuj6gpLttDT0twqhTQPyXPJxw5a96x7WHKfjmdC3IJB/fC1LLOyOzn8bFeRLtR0baGigh2okoaCpFTRRdp7xzH2cjx0VvT3J7eLW5WbsVK+mogJDmeTtSHx5D2LUWOh9Mq2tI+jZ2nn7lz+TmSsl9Pg9H6Z0uvDx07FuRudnK63W+1PrLu9kD3DP9HGQPNcg2lvsdRcJ5GO61rnktcRjIR7f3s1FcaeF/0MWmh4/v8AcFh5pyTxKuYKeu5+TD6soRm1vz7FhUXQuJwxqhSVbpCAAMnuUMuzzTkWI2mR5A5AErWg2zkr1D2RKfUCGPcae2eKbbVv0G8fYopBJyTklTrdThrTV1GkLNW+JT022VXXGK3osoqp1vphK938ok9VueCrJ62WbWSRzjnOScqJUVD6iZ0jzx0A7h3JGchDs+BIY6XLXIcj94pEbHSybrNT8kYaXuDWjJPJSZC2maY4zmUjtFN88skfHAT5GwMMUJ7X1nKPvaIsIYRvYnboA1Urb1rZZbCSM/8AM9OPcXhRgMFTNsW9Za9nKtjstFEadxHJzJHZB9hHvUN/2ljF5sSZW7GQhl+cATh9HUt1/VC0Vfb3Qb7s6N1VJsMx9TfZDu4MVFUya88MC1dzrYqqCYtGC5hOvkse+uNj2/J3PRLZ01OK8bI3QhTmXaqvkH1Wv/BQ9vIf+cahvPVan+D1SiWW+VWPVG6PMn9io9t4c3+Zp5uK0sNfQkcZny3kyf5MLf29dX254H562wO072jdPyVfNTui4gq8rYerobJUvGlPUTUEvgN7fb8H/BWV/trRSdYwa4yrVVaknsq23dkor5MVvYShIikaWuIKbyq846ZajMkMcrG20z6qojiiaXSPOGtHElVLCri0Vb6SqhnhcWyxuD2OHIjUKCe9PRaoacls6hdeh3aOgomVEUcFZloc6Ond22Huwcb3s9yw1ZaamimMdXBLBIOLZWFh+K9PdFnSFQ7Q2+OnrHshqowGuD3cPAnu7j7Drx6NVW2kq49yopopWH6r2hw9xWL+7uqlqRqylV4lE8LCjdyHwS20bu5ey6jYHZmocXS2ShJPdEB8k2zo62VYQRY6HTvjypF1KXwN/wDTfDPH8NKS8NA3nHkNT7lstm+jjaK+Fpp7e+mgP8/V5jbjvA9Y+wL1PQbP2qg/6Fb6Wnxzjia0+8BVW2u1Vt2Vtz5amRjqgtzFAHYc4+PcPFNefbN6ihE6m9QieStsrFW7LX+a13B8MkjGtkZJCTuva7hodQdOCpWVZHNWG198nvd7q7hVv35p35J5AcgByAHJZsylbeN3di7/ACZ2YoqeolyK096S6rJHEKoEuvFKEmeatIzmWMlSSOSpr0/NE8facApYy7gVDusbjJSQgZc9+9j5In9rEh9xsKb6Gz2qHm2lDsfrPcVeVbT/ABTa8f5YD3gqmrgG1AiYezCxsI/otA+4rcttxk6NKybdy6J7JM+AcAfmmWfbomol22KX5Mrsfn8kQjnwVvtGx42amY713VdOBnykWf2WqRDQRHucdPaVbbZVT6rZR07Run0yCNuv6MhXL48IrJ7n8np/UZTl03tXhxM1SwCOtgD5GlxlZgDXXeCn7Ynf2vvbhwdWS/3iqbZWGSq2mtcLjvb1TGXHOgAcCSfZlTrpOKq6VtSDkTVEkgPeC4kfBdVXLve0jyi+t1fTJ8kTgEM4RnCtqGgigpvT7oCIP5qL60p/BWEm/BUlNR8lfGSIi84Dfq+JVzsbQw3Xai2UVUf5PPOGvGcZGp3fbjCoqiczyl5AaM6NHBo7kqlqJKeeOWB7o5I3B7XN0LSNQQnKXGhk4Nx4PWzKaAUQpWwQim3d3qd0bm73bvDC80bf2+ntO1tzo6IBtPHL2Gg53QQDu+zK1cXS5dxbzE6monVWMekEO49+7wz8Fzivq5ayplnnkdJNI8ve9xyXE6klRVwlBtsqYtU4y3IiyPONCVeSP/Ltt3//ALhTjB/TH7fmqIglO0VRJR1LJotccW8nDmEu+efBflHa2vKGG5ynmOwrK9UzHBldTawTakfZd934qraorIa4LuNkb0ywpah0MjZGYy05GfkuuWatZtHs+GcauBuW54uHDH3e5cbj1C0+xlzfbbnG4HsOOCP37/wWTmUdy2dl0nM39DZPvVDlriB7Fz+5QGkq94D6N5zjuK7ftHQseGVUABgqG7wI5H99feuZ7RW/fY9oGCeB7is+ibjLRvZNccmlx914Kmx1IjnMR9SXtDwd3La7M2r8sXWGkDt3f5rm1MHhpGolYc+IIW72drpG9TWU792Qa5HI810NEu6J5p1Gj0rG17nV7hse22W+S11kgnpauNzeGo01/H2LzhfbVNarlU0NSMSwPLCftDkfaMFdkq9pblVT00tS956sgtzkKn6XbZHW0NFfqRuWloimx3H1SfI5HuWflVuE1L5NbpF7uodU3zH/AIOOPGCmJNc5U6WPXQKOY+OQmQ2SXxXkguamnNWhsVBT11wbBV1DKaJ3GR/AKvu1NFT1ssULxIxpIDxwd4qaJRnB67iqLUW6nS1FjVPK7Dgp3Suw0ZKmus84ZvFunktP0dWyG5XimgmIDHvAJXoy+7D2QbNTdXTMieyPIk558VbhTHS7vcy7811z7Ujx3PAYyQVHcMLQ7RxMirZGx8A4hUEmMqrbDtei/XPvimNIkopKiJAIxxQKAQApBEjCEAaMIkaUAwlAIglhGh6FsCkRhNMCkRhRyZbpjslQZ0VjTQPe5oa0ue4gNHeToFCg0wuidHdKytuge+MGOmAlcT9r6o9+vsUUtaNfGr7mkXm1Jbs3sZSWmB2J5m9U4jTJ4yH36LFWe3vr5RFECXHgFP26uRuW0UrQcxUo6pvdn6x9/wAlEtFTNSVDJIHFrwdCOS18CpVwW/c5rreS77ZdnhcIKsoHU0hieMOBwQe5FZ6I1NzDnjMcPbcO88h9/sWoistyvb3TU9M9/WfzjzutwPE8fZlaCg2UhtVIG19dDHKTvSBuOPdrg6DwTM+Ln9MDQ6DbTRqeQ/yQ6RmG5OpWhuU4sOzpaAfTKgHstGXcOXkNPMqtNXaKMjqxNVSNOmhx8d0fAoTbT1Ujv5PTNY7k55Lj7hgfNZcOnSeu46DN/U1MuKlsxP8AF293KQyNoZWb5zvTERj2b2vwUgbDvhG9d7pSUo47rO0744+AKvqitudU0tlqZI2Hk0iMe4Yz7VWeigEney7OCf281rQj2LSRyGRlyvk5SY5bbDYGTtjghr7rOfVbg4cfIY+9bi27KXl8OLfs1SUcRGnpAaD7jg/BF0UWmubtNT1sdPK2lYx4kmLSGkFuAAeeuOC7a1R23Si9JmdKzng847UbKdXOynu9rZaqqU4irIBiF57njJGP0hgjiRhYC+MkjndRvjMXo5LHRkYIcNDnyXr3aC0Q3uz1NBUNBEreySPVf9Vw8j9688XfZutvlVFPA2OORjDT1ksz91rHx6AuPeW48TulOqyOGpFiip3taXJzRzNUW4uhjYaj4S7QU4d+hTvI9+U/BsLb2u3ztDCQP+6u/FI8ute5qf6Vka32mBYwU0O8fzruHgopaSSTxPFdGl2Ltz3lzto4vAeiO0+KQdiLby2jj/8AKP8AxSPNqfGwj0fI89pzzcQLCuh/xHoDw2hhzyzSP/FUm0Oy1XZ42TudFU0cpwypgOWE9x5tPgU6vKrk9JkV3S7qo90omWxhPQ1Do4nQvayWB5y6N4yM947j4hE9qRjVW1yZU04svti46Vt7eYYnxSSUlRHjfBacxnThnkqSsmkjD49MajyTtDVS0NZDU05AlidvNzqPI+BGQrKq/Jdzd1hcaKR3rMeN5oPg4fes/MxnNqUDpeh9VrohKq5+ToH8HWiLNkrpVY1mqi0acmj9qynSFEIdoHOJxl2V1PoYpIaPYWKCGRkgMkry5vAkvI+5c96W6R0VeZQDx4qahOPBg22RlfKXtsxtwtxqoqy2sGBcmNnpT/3mIHDfN7S4DxwjsVZHerH1chxUxN3JGniCOasKIRXa0Gnc7dlZh0bwcOY4cCPFZK8NqW3U1cD20l3/AJ1pO7FVH7YPAOPNp0J1Hcrkk6n3rwU9rITg3prwU91gMFXJG4cCoOFbXGvjqH4udPLRVfAuLew5Vzmt+pIx472u4qCxqXKLValFakhtoUmF5CZwe5G04PNQNFiEmmXlruU9FUMnppXxTM9V7Tgj9ngut7JdM90tkbIatvXRDTskEY/VPD2EDwXDWPIUmKcjmqtuPGfk0asrS1Lk9YW7pwtEsY9Jj3DjXRzfuI+KkVPTbZGMzFHvHuLnfc1eUG1TvtJRq3HmSq37CBJ6tT50d52k6cqydj47XGIARjfa3B95z8guPXzaCsu1S+esnfJK45Jc4n5qifOSOOFHdIVYqxYw8IbPLSWoLQ7PKXE6lR95EX5PFAAk6DKvR4RmWScnsMHVLa7JQbDIdRG7HkiOGuALwHcmjtH3BSbIdF3YqeOWcOqXBlOwb8jv0Uq3AXfaSe6ti3aOnOIWY0/RHvHwKOg2ZuNbStnuZdabRnWaoBa6UdzGcXeQ94W12eoaORrRDCYbdSjMbX43nnm53ie7kNFJFOz6V4Kl044+7JPkz1TE6Goa2TV51K7jszbRW9HtfS4BMtM8Dz3cj4gLjNYRW3z6PBBfgYXonY+IUthjY4cWgH2qLJWlpD6LG1GTPMtgO7Ssjdod53zK1V5FO/YyNs7ZNx1waWhhAJ3YnZ4+arzSW6211VHPWNf1c8g3Yu0fXKh3i6Or+qijYYqSAERR5ycni4nvOB7llYmBP1/Ul4O56p12j/Tlj1vcmkQuvEcboqWFsDXjDiDlzh3F3d4BRnaapwq7ttvgo6QXO7j6LjDAfWlPl3LfUfZHn1l2uZcsattBDS0rbndhin4wwY7Up8u5VtzuE1xqjNO4Dk1g4MHcEd1uE9yqXTTnhoxjeDB3BQ8JJS9kNhD+eXkBVxT2Yil36l/VTSD6GM8T4lSKOkhtNO2uubd6odrBTHj+sf3+KqKqtnqqs1MshMhOQe7wA5BKko+RO5zeo+BhwLHua4EOBwQeRScZKtqiIV9L6VG0CVgxK0c1BZHnCGmPjNEmzVDaaqBkAMMg3HgjOiXdbYaOpLW6wv1YfDuQhpXHGGlaGipvTbcaWX87HrGT+/sUijtaZXnb2S7kUdmeMvo6jWCbQeDv3+KgVFI+mqHxScWnj3jkVdfk1+9wcCPgrasthraCOoa36eLSTA4j99faUx1trQ+N6hLa9zJRRqdDGQNPYrKK1OH1VKjtjhwBVeyjuNfDz1B+TabFVzbpapLdUHEgBcwnkf8A319pVHfLa4h4c3DgcEJzZyCWhuUMrMjtDlz/AH0XRLzZRUNFTEzsTNzw4FYl+I4TO5xOpwsrU0+Tzzcbc+Gs6xoJa7jgc1ZbPSGlqnQvHZf228vMLc3C1yU75C2EPdg4DhkZWQNJIcStaQ+M72Me8LTxYvWjneu9km5L35NdtHtG27UFFT+ixQ+js3N5gwXDxT1g6u9WSstNXnckYQPDx9hwVTMojJG14acOGQrCwMdRXOKQAhpOHeXNS34/dW0YXTc1UZEX7eGctqLVUR1stK+JxnieY3NA5g4UStt0lM7dlaWO7iMFd0u9NHs7tpRXw0rZ4JW5ewjQvaMZ88YPsWK2/rW7RX2euhpRA1+AGNHdz81Xqq7o7SNXLvcLnD2OXSRkHQlRJWHXOq1ktqfjO44+xVlVQOjzluErpaKrtT42Z8tAznuTBGFYVEOM6KE8EFMa0I3ssbLc5LfO2SNxBaQVuK/pJuVVbvRZKl5jxjBK5kfAoi48ypI3SitFazGhY+5ofuNUaiVzjxKr3JbykFQTl3PbJ4rXCEHiiclHiiIyFGPCQ5II0AElhJASkAGEEY4IBKApoTrAmxxT7AhksVyLYNVJiGqZY1SomqGbNCiJKgbnRdX2WYLBsTNcJhiSZpnOeOBowfv3rm9mon19fTUkYO9PII9OWTqfdldF6TallPbKS3U+AyRw07mMGg9+Pcoq4+pYoms5rGx52/g5/A5z3ue87z3EuJ7yeK630b7KU/5E/jDdomysllFPQwSerJJnG+7vaDnT9EnuXJIRjhxXoGoqGQ7D7DU8J3Y9+FjvAvie0H+s5bs9pJRODsnztl1s9aJtp3S1ElRLT21jtxvV6Ol/AfAZAAWrpdi7BTN//T2Snm6Yl5UTornZLsZSBow5jnseP0gVrTqs6c5dzEcmzh20Ww10o7rLFQUc1VSvcXQyRjPZ7ndxHDVO2/o3vdSQajqKNp/yj95w9jfxXbEeE9ZE9aE2znlu6L6CPBr6ypqHc2xgRt+8rU23Zay27BpLdAHj6729Y73uyroBKAUUrJS8sVRYjdwOGg5IsJzCIhM2OUBK5bt5SxU1fUU9PGGNlLqo4+s/OvwXU1z/AKRGBtUyoxkxPG9+qRhN3zo6Ho8O2bf4OWyk7+AkySFrcZWh2YtdJcdrqW31ryKd7nZwcF+ASG58Va9K2zlssclDLa2mE1Bc18BeXDQDDhnUdyWWk9Gz+41Yq2YLf1SmvJPNdU2F2Isl22QhrKxjpamcOLpRIR1JBIwNcDGOaxWxdoo7ltZTW+tlzSue/Vpx1m7nAB8cKPh7JFmp934KQOI1yVbWtrbhS3G2zaw1VLISDye1u813mCFpOlXZ62WKWhfa29SZ94Ph3ieGMOGdR3LM7Mn+Xv8A9Xm/3ZTNLholhcr6XL2aOSyDIBxxGUwRqpL/AFWfqj5Jhw1XQw8I4TJSTYlHjwyUAlAElSpFFnVuha+CCGpt8x9R/WNyfqu0Pud81YdKtGyponyNGTjOQuUWavltdwiqotS3Rzc43mniFtr7e31Vrb1bxLC8ZY/vHMHxHBRShqXcLW23pHL7fcJLdXEE4bnBCvayGmvMBO6CQFQ3VzOucQ3BKr6e4TUjvonOb4JYZcPtkXcjpVmlZX5JlTS1lvBja4ug+w8Bzfccqqe2mqC+U0FP2d2JzWbzBnBJdoeP4K0nvsssYZIAR3lUMNSGyVQdgbz2uGvDQqC6yttdotNN8Y6sQ91FAf8AEpW/6OpI+YKW2lt5+rcW+UzT82pj0uPPFH6UzllQ90CwqrCU2jtx/n7m32RlLFDbudfcR508Z+9QvSm9xKP0kH6rknfAkVNhPFDbf+1K8edG3/iTrKC2Y7V2rx5ULf8AiVaKgfZclCo72uQrIDvQt+C3Zb7N9a7XM/q0TP8AiTjbfs+CC+43t36tLCPm5U4qR9lyX6U3mHJe+AjosLkU+zLPWk2jk8jAz7inY37LswBbb7Nj/KXJjP7rFQ+kx/pBGKmLm5KpxGOiZe3Cs2eNqrY6bZrcmMD9yea4SyujdjRwGgJClW/ausoqKBlrpbXbiI2gy01G3rScDUvdk5PhhZWqnjNJUBrwT1T/AJJ6ndmmiwc9gfJHqwTBY05cItKqtqK6qNRX1E1TMeL5Xlx+Knflqo9FFPHhseMacVnC+UOGBorGmmZoHDVOeWofaEekyyH9a8Gu2GpvSbk2WTUA51XaL3fYrNYnzAj6CPrMd5+qPa4hcR2XqJmVYFM09rAxjmtBfdqJYJPRacQTlv550jd8F32W68vn5KWC9XTZn5dbobiuTBl+88ue4F7iXOJPM6lDeHePetA/aaqJJ9FoP7H9qT/GWrH+LUP9j+1XFGK9zO9Sz/xEWyhhoqZtyuzcxn8xT85T3nwVbc66e41RqKkgk6NaPVYO4I7jWz3CpM9S4FxGABoGjuAUQpsnvhDoQ575eRBC0FLSQ2SnZXXGPfrHDMFMfq/pO/f4pdLTQ2OnZXXBofXPGaemP1f0nfv8VRVlTNWVD56h5fK86k/d3BGlDn3E27XpeBNXUzVlS+aofvyO58gO4dwTYCPCMJnlkySS0iwtM3o1Q1x9R2j/ACVnPbOpqQY9Yn6sx8lUU7Tpot7sRFFX3Gho6kZYZ4wPLeGR+/epotKLb9irc3F7Rd7P7DQi2x3C/wBV6DTSaxxhuZJPHHIK+orVsfC9rmT1xc3gSAn9sq6mnvVRR1h6mJrurjnb/Mkd45t7xx5hYW5sqbdVvpqkbr269k5a5p4OaeYPIqtBuz7paZUak+VyjoUlo2QdJvvkqg5w3sacFYts2y9vmMRmqN57GkggEYIyPgVze2uFfAIIZCysGd1js4m5gA8ncsc/NWzqg3qNhhJbdIY2xup/8u1gwCzP1wBq3nxHcoprtf3PRZrjKUfC2bCawbMR0xmMtRuB+5wHHGfko7bbspnSap/qhZu21brrb5LUyTq64yiWDf4SODSDHnkTy8dFnvTJA7BLgRyKIRbbTkx7hJaaSOrUln2ZEBqRLUbjXhmcDjjK1lDLZ5qJ0MbnPjxnUahccpq9w2RnJcc+nRj/APhuVts7cI6GjgqqqpDnVBLYadvHm0uceTcqndDhtt+TawO5SUfZm2r7Zs/K1z5PSABxIxzWbntWx8UuXGqDnZJ4IrlVFlI2EHLpAHOd3Y4D8VmKiGJ1K6rrppo4mP3QyJoL5O/BJAHxUdViXls1s3p9kq/O9GrNu2Wpo443emNBbvtBxwPNIFLspnQ1vs3VgLpfJK+vZLuiONrRFGxpzutHAE8z3lW9rhhZb3XO7GVtIcsgijIbJUO54J4NHM+xXXxBOTZykqnGzUUjoNXT7N3SzmKYVUkcPaBGN4ED8Fl3WfYnma8+1qkbNXmzF00DKGqBc3LRJOHD4ALAXcyU10mpow5zus3WNaMk5OgHfxChqSTcW2jSuhZbVG1c+xs32LYuQbrH17CeB7JwsbtvsJ6JSCvtszKugfkCVowWnucORVztBaG2W0U0764GuLwyWny3snGSABrlp0P3K02LqRcqK42+py6CalkJHi0ZB81LCalHvg9pfJnWq2maUjzjdaUxPc0hUNQzBW22ljHXuKyNSzU6IsXJp0yco7ZWP0TTipEo4qO5V2SjbkhLKQUxigKTlHySU0AJSII0CgCNEEoJQAlBJTjAlQIcjblSY4ySMBJhYrGlhzoBlOUNksZaGmREclIijVnHQSGMODD7EgwlrtRgpl1LijQxrE2azowoOtvMtU5vZpoiQe5ztB8MqLt1V+mbSzNB7EAELfMan4la3o+p20Ozc1XJhvXSOec/YYMf8S5457qqsknf60shefacpenVbm5fBN1y308eFS9+RMDcvAXULfXflPoydTNeG1lC4iBoOpLHdZGR8lzNjd0k81uui6r3LxWULgDDPSud5OZqPeN4LVskotI5X9u7q3KPsdU6IrsyW419NGcU9axlwgA4DfGXAeRJH9FdTwvO2w9b+R7pSyA4bbq005BGCaebMkZ+LwvRfIEHIWbkx7ZkVfKBhABGlYVbZMohAIAJWEE3ZIohYSHJzmkuCEx6iN81ittIevnqIyNJGbq2jtCqm9Ww17Q+I4kHI80Phpmz022Nc/qOE1u+HRS5c2QaEg4Ic39wo1XUVFXJ1lVPLPJjG9I8uOO7XktVtbZpbfVytlDfpPpmge5yz9LQPqXODC1rWDee95w1je8lSuSa2bnam+5DEFZVQQSQQVM8UMnrxskIa7zAOCmA5zXBzCWuacgtOCCp4prfjW+2kf8AjIxTW3nf7T/bfsUW/wADkq15aIU889TL1lVNLPJgDfleXHHdkq32a0rnk6NFPMSe4bhUUwWwcb9aceEx/BVd62goqG31NFZ5jVT1Lerlqg0tY1nNrAdSTzKRQlY0khtuRVVW33Iwknqt8h8kyU5IclN81vwWkcNfNSkwAI28UMIwFKkUmw1Nt9dJS70RHWU0h7cRPPvB5FRAMpQCXXyN7tPgtha6K5H+RysMruEcp3XD38fYsTtJbai3VBbJDJ5lpAWhzp4J1tVVNaGNnk3MeqTvD3HRVZYkG+41F1i5QVb8HMZ6iTJBz5JgHJdv94PFdKlpYah29PTwPJ5mMfckCz0ByfQ4gTzBcPvUbwm/cauoLe2c+ZKxuuMpfpbW8guv7HbDWW8envqLoy1uhaMMPVvMuQdQJOQxy71zPbCywW24Sx0ta2oaHYzutHy0VOzHcW1sv1dQ7/tRWCuZ3IxXhT6HZ1tRbnVPpQyPqgA4VJUUz45SwP3scwFHKhxXcySOfKT0mThXjw96MXD9yqwQyE8T7lJp6KeRwG+R7Ao1D8Ev7yz5JguGOPwKU24jPBXFl2VNYBv3RkH6wb95V3JsQyNmRtDDnuLYz96d6Qn7+aMgLizGob7kJKiCQatGfBKrLS+Oocw1Ub8HG8A0feukbM7C22bZmprqu/Qumjjc9tI0Q9sgZDck72vgnKnnWwn1GWvqSOUVIaI5CwnG6RhHDVyRgNaToMLoD7RQBpBo49eIJP4ptluoo3ZjpafTvbn5q6sGS8sy5dSjvcUZy2TzVD2tbG9xPcMrd0Gz7xTtnuTI6WIjIfM7dJ8hxJUaConp9Kd/UD/NNDfkElz3SPLpHOe88XOJJPtUiwIPlk0OvXVxcY87+Swmro6SJ1Pa8tyMPqCMOcO5o+qPHj5KpGgwnSc80khXYwUVpGPZZKyXdIQRlJISyElwQMEFXezEcYNdVvjbJJSQ9bEHcA7XX4Klwr/ZsfyG9f6r+KI+SO5/QUVVUS1dQ+epkL5XnJJ/fgmglEIsJjJ1wuAsJTBh4JGgRgEnQKyrLPV0VFSVVTCWQVbS+F5+u0HBIScb0Lt+UX20W0FBdqOigoLXFRGFuHOaBl2g7uXmp+wLsbSWn/Wov7wWLgb2gtlsMMbSWkf96i/vBOjFRg0vgrZdrskpM3u29HHV3SudQPe6qje98lO8DLgCcuYRxx9njhUtou9A3Z6pornSvq5RvejHdDg0OHAOOrQHdrRWm18Ec1/mdb6qRtwZMXBj27uXBxwGOzx4YzxUax09LerxBHPA+Gd7j1/V4EZx6xA4gnByOGeCp6TglLwhtTcdyWtlHabNXVjf5NSzTY4lrCVcVNgvU7YnuoKn0lpIdKGHedjG7k947+K3dotk1/hdMaqagtEbzFTU9IdwvDdC4n9ydVYM2IoC8A1921IH/Sv2Kjd1WqEu2Rdq6dkTj3RMLBZbtJtLT1j6KpDetie95ZjUBuT7wVWTbKXcyuIoKgguP1D3roVi2VpKy1UtVLXXTrJWbzsVONckd3grJux1D/166/8Amv2KJdWpT2n/AIJ/9PyGtPRzpuzl0Gz0tMKKfrXVjJA3cOd0RuGfeUmXZy7dRbRHRz70MRDuyRg9Y4j5hdJ/ifQ/9euv/mv2IxsdRA5Ffds/61+xM/1Ognhi5UGmtGSkoagUW7NE9kjNd1wxos9eGFzA0gYbnGB3rpbaeW2XGmttZUvrLfWhzIXzYMkUg5E8+PHzWbvNtZDM5otVbUFpwd17t0+5v3pjsj90fB0WNlyuThYvqRzugt0FPBJX3jeFvieWxxtdh9U8a7je4fady81Pi9JvoluNfU09DRR4hjfI0iNndFG1oJOBr4cTqVIvdpq66tbXX5klvtdNGGnsboa0HSKFp4uP4kqJE5t3Y+urybfY6QGCCOEb2DxEcYPrOPFzj5nkr1dncu7Zz+ZSozaSJtupbfS1kcov9E7B1HUyjT+qlbUVcFjc2voHdfdZgYI6kNIZTjHrNB1LyNAeA15qsDtm8/nb1n9SEferW6/kGtsW9Ibq6NgEg3REHZGh54SXfcpPbJcB91c6v9zn0TiX5JJJOSTqSujdG2fS6n/VJv7qqrJJsUygrG1TK8zEfRmdwMnDQMLOyNftLUbCG0l1QaGOtbKaWbWaVjhjc19UKZXqUJRSaM7Iq5TbOCbRayOWVnaDKGnmtVtEcSOWTqyd/TKksemWaF9JebY7IOsNltVwfV08zbhH1jWRuy5g7isQ8aqwq55XxhsjnFreAJ4KA4KCbTfA6EZRWpPY0U2U47mkFRsfsSkkapR4oimCoIcEaII0ooYRhEEaADCdjGqaCdZxTkKkTYQtBs/HHJWRNkIDSQCs9CVZUUxieCOKmrkovkWUHKLSPUFPsrYW7KtlDo+t6vOc88Lh18pY4qyVsIy0E4wig2nrhSCDr37gGAN5Ksgdcr3Rwk562Zodnuzk/AKW6yPY+didKw7a7dzfDNteozati/R2jdc2nZDp9p2M/MrAUdMTIwY54XRNvXGSipoQPzkpcfID9qp7LZX1D48NJ1Cm6ZT/AAu75I/1LmqOR2f+KSMsacg6jmVoti2PpJzXNHbbK0tzzDdSPbnCkVdofTmUub6uQry2W8UtDTxn1gwE+Z1Ki6luK4Nf9Kwhcm5eNB11tFBfqiCnDvR6+N0cJJzl356A/B7Pau6bD3MXfZa31W9vOMYY4+LdPwXE9qn1Ys1tqqdzT6JvMaN3tCWNwkj17iMjHgt30PXKL0m42+Bw9GlDa2mH6DwDj2BwH9FQ3fxKlMwcir9vkTqfszp+EYRgIwqAsUBBHjVRauvpKMZqqmGL9ZwB9yFt+B7aj5ZJRELN1m2dshyIBNUO5brd1vvKoa3betlyKSGGAd57Z/BTwxbZ+EQTzKYe5vns7khg1XJa+7V9cD6TVzPafq72G+4aJzZ27z2yvjd1jvRnOAkjJ0Le/HeFZfT5qDe+RKeoxcta4LvpGhhEkNXUyNip4j1csjuQcBoO8riO117lnfJb6eM01DC8tMee1I4H1nnmfDgF6T2ztLb1snc6JgaZJoS6PT67e034ge9eXNomGU01YWkekxZf4SM7L8+4H2pmFXGW9mzf1KTqUI8Io3yHPE+9NmV2eJ96KTimitFwRlvIfyPdb4nKJzs+aZJwrjZzZ+6bQ1JhtVI+bdOHyHsxx/rOOg8uKRqMeWNU52PUeSpOUMLqFN0Y0dMzN6vzGyc4qOPewe7ed+CN+x+x8Wklzu2ftdj5bqgedTF6bLkOj5dq2onMAEoBdBqdhbTUA/kTaOF0mMiKsZuZ/pD8FQt2PvBuzbeaUiRw3utB3ogzm/eGhAU9eTVZ9rKOTgZGN/3YtDWyezFy2nrzTW2Ju6zBlmkO7HEP0j3+A1K7BaOjfZuywtfdnOutUNT1hLIgfBgOv9IlWHRzb6a3bHUfoD3GKcvmfI7G9I7eLcn2NGByCG0VZHDA4bwyVmZWXJtpPg3Om9KhNRlJbbMRV02zF8ZrQMpKmEykx0o6t0gYN4NGNNW5PD6pWMqtrdlrcXMotn6aYjg6oLpCfeVZXelkM5qKKUwyNcJGPbxjeDkO9/396xG0VrirJJ6ykhEFQ3t1dG3+aJ+uzviPEH6ucHkkws31V2SfJN1voX7aaugvof8Ahjtf0hsc7FPYbRG3lilGfis9VbX3SqefRaGkaAcfR0rVBfSZ5FFAyWmeXRnjxBGQfMK5bK3X0GNRTR3JWeDT7NbVQNikg2j2Xt9wOS5s80Tt5uQMNAaQAPFZXaOJldXySW+xx0kJOjYt7HxJV3TVlGR/KIHsf3sO8PcdQrKGptjv5/dP6bCFi3ZGTH7oHYYnRemXJOF+jn3oFSBhtBMPLKIWupcdaCb3FdMj9AcezV0/9bCmRQ0p4VVPj/SBVX1C5eYGlH9L4kvF/wDwctZZ5+dvnPsKmUtoDXDrrXM4cwd4feuoxUlO7hU0vtlCkMtsbuFTRjznak/1Kz/wHP8ASuIv/wA3/BkbPbbGMel7PRyeL5ZR8nK2q7Zsv1B6vZunDscWzS/8SvhZ2nX0u3+2qj/FPxWaHHbuNoZ+tWx/in/6ja/FZBL9NYEfuyDk1bZ4RUE0trm6vOgbvY+K0tmrKG1W57hsvBU1eMNL2PLge/O9jj4LaSUFtjb9Lf7MzynL/wC6CqusnsNOMflKSsdybS07sf1nYClhm5MvFZXn0PpSX1ZBjhtHtABmS205HPNCw/crC27dzMjb11otczjydRsGEi51LqsOZSxGCE6HLsvcPE8vYq1tvI4NWzjTvlHdvByufi4Vc+3Gfcvk2VPttbphit2atbx/m4urPwK0Vji2SvG9UtoamjEBa6Rjpi6J2TgDB17zx+qVz2ktb5Do1oAGXOJw1o7yeS11ho3zQxRU4IomnfDiMGVxGC8+GNAO7Pem5mUsetyb5HdL6T++vUIrj3OqbP2nZXae0zCps1PEY37kcsLRFLu40OW4188rJbYdFtVb6eStsEzrhSsBc+FwxOweAGjx5YPgr3ZydtsHV8nauPeVubdViTddTyEO44WVidSn5bOg6r0Gnb7FweWnanTgk7q6R0g7Js/KN0r7Qx+Y6k+k0wGd3ew7eZjll2o9qZtXRvUPgbUXy40lqjP8049ZN7WjQeROV0f7qtQU5PRw8cG6drqrjto57uq72eOKG9f6r+K38ex+xEDcT3S5VT/tNLWD3BpUil2U2V6qphoLjXU7qlnVkylrwPLQKuup4+/uLtv6dznDfYca3dEMLfX3oxvFDE6e2viutMBnNOMSAfqc/YSsI5ha4tcCCDgg8QVZhbCzmL2ULsayh6sWhIUh1RLLHGySR7mM0aCcgeSj80tqk0V2yRANVsthh/hLaf8AWo/7wWQpmkkLa7DMxtJas/8AWo/7wT5fY/6FK5+C822/+Yrhnh1ztPapuwtVLPtBH1u64ljyXGNu8eweYGVP2rNI+8XJ35CmqzFI50skc8g3Rk6kAYCY2Mr7dLeoY6S29RI5j8P9KdJjsHkQqbs7q9a9hIwcd8mv2MvMNNs3SQyw1znNLxmOkke09s8C0EFXrdoaRhD5Ibk1jTvOcaCbAA1JPZVJsNIRsvR6HjJy/wA45aKGYiWPG96w+a4TKkvXl/U7jFX8GP8AQjbKSNds5bXMc1zHQhzXNOQQSSCPYVbCTxWa2OeG7M0AAwA1+g/0j1diRVpS5J0hdfcYLfT9dVSFrN4MAa0uc5x0DWtGSSe4KO2/U5/xa5/+Qm/4VX3R5dfbCNSA+odjxEJwfiferdryBwd7k5PQa2UG0Nyjq7rs82KKqY4VhP01O+IHs8t4DKhbUeiCumM0tbvF7vzeMDXzU/aZ29dtnMg6Vp4/qhJv1RUl8xivEUAa9wwXOGNfBq3aPqx4kGOv48kc6vzbI6NslY+8SMjdvFsbY8kcwCTp5qtdO24GO6XSEU1lpsw0FvjOOsI16tvPHN8nHlxOmluNXcNyQM2qp4nYOCZJNP8AYWUrKL8pTxy3Ha23VMrG7odK6ZxAznA7HBXsVrw2QdSh2vaHaa+3Kqqo4qaGhD5XhjImUUWAScADLfmt1b7dtEKeSKopKeVhHYkhp4nRuBHLDddVhoLNSNcHN2htoIOQWtm0/wBhaS1xtlqppKraCmq5XtGXETOOnm0KxkKOvo8f0Zn9PbVupe5CbTbXx6C2RaaZ9Cp/wWk2YdfmGq/KtIIYfRptRBGzXcOPVCxV2s9ohq5+tv8ADHMXbwiFHK4YOurlfbCUcEUlW+GtZPikm0bE9uexx1RWk4t//RFmJxlo4ZtCfpHLNdYIapkha14a4HddqD4FaK/DMhWcq4XjtFpAKtWb3smo12LYm/1zbncZ6ttNBSiV291UDd1jPBo5BVDgpUgwE5b6YVVXHGTgOOFDrueh02oLZVPbplNOXVukLo+j2as9FWNrIZ/SGb2GHhpn71yuQYJSWVuJFTdG5biNHiidwSik8QoGToCCCJCFFBGiCNKgFNTjeSbanGpdjokmMqZA7goMalxJvdosQjst6fBxklbjo2pY5NoGyuccQRPfw5kbo+awNM7guldGDAIrlUHuZED73H7k2dv0vg1cGnutXJqbqKGputNFUySN3GZ0aOZ/Yuk7F2W0GPeif1rsZ7YxhcKvVf8A4RT4Jw0Nb7h+1a3ZXaJ9PLC0PIa5wB1W5CpyojGL0cB1lOWbOx8rZv8AaWz2nrtx0m6Xvxhrc8VS1tPRGU9W9+Afsqk/K76q4xFzyQHOfx8CnpKgEk5WflvsSi3s7b9K4k40ufjZPu1DFJsvP1bgSCZml2mrT+AKzHRpdRartbJS/wCjpal9E/xicS6M+WHPH9FaHaCu/J1ppH8THuvI79RkfErESxmHaCtpYy3cqoz1O4MAvj+ljI82Fw9qXF/iUuLKP6gp9LJVn/keqwsptJtU631bqSjiY+Rnrvfwae4AKx2KuYvOy9vrN4Fzowx549puh+WfasNtjSuptoasHOJHCRvkR+IKgxKozt7ZmHmWzrrTgIq9obnVgiSrkDT9WPsD4Kre8udlx1PM8SryK207LRDWiKqqNBI9zMGMdrtMcB2hpzV+bNQwzVzINw01a1kLOZic4EjHnlpH7FdeTVVxGJSjj2W8ykYSenqIomSywyMjk9RzmkB3kVPgtB6lkstQwOMQqHQMaTJ1OfWGdCfBWtcH3GzzVVVv05bGHlzZ96J729nd3Dq13HQKFQ3SkjipZ6ozel0kL4Gsa0FszSDu5PLGSnevZZDcV7+w30oVy+pk+kpbW2vt0cFO6ZlXC5zJKh28N4ggAtGmjh8VUbRMpmVMQpxTiXqh14p/zfWZOQ34KJBcJI6Okga0B1LKZI5c6jODu48xlNzSPqJ5JZD25HFxwMDJ8FJRjzjPum+AnfFx7Yo6nshVmusNK9xzJG3q3Hxbp8sLz90l2gWy53uha3djhqBXU+n81Lo4DyJb7l2/o5jkZbKpzgRG6bs+wDKyfThbGdfarq8fQvLrfUn/ADcgOCfI5WfVJV5DivBrVtyqTZ5ze3JTZaQr30emtrRJdWPkeSWiEaDQkanxwdO7zWhNutt02ZmuFLBTAU/5yOIbk0Y+0DwdjuI9oWpZLtW2RQg5vSIXRvsW7aeqfUVhfFaKd2JXt0dK7/JtPLvJ5DxK6Dd7q2kDbTZ44qSkhG7uxDAb+3vPFWM1ZQbPdH1A2zyB9P1IEcmMF7j6ziO8uzn9i5a6uke5xLjknJK5fqebJy7Ynov6Z6PFw9Wa5Og0D6ZjO0A954knJUa+0FJNRy1AcyKONuXvccNaPErFMuUlP2jIcd2eKqrhtDW7RVDLVRTCOBh7cmMhp54H1n+PALNqUrn2pG9m9uAvVlLSKTaTaCKkmkjpA6R/I418/BaLoR2jq5Kuuhq5HdS+KVzWknskNwPvVbtPsdLZrSKrdzERlz+JJPM95UHo5aaaeoe7lAdR3kj8Vs42J6HKZxXUusT6m3GS1FHeNhK8QdHNo3iQ4RP/AN49Zi/3J88ru0cIWmv6nYmzRN4up3Ox/wCK9Z+4yucHOwTgZOAs/Ltbm4o6jo+JGulWSH4KnclBOPakXmww3iJs1C90NVH2o3RnD4z+ieY/RKzZuU7aiIdSDFI8R7zHbxa45wHY0HA8+SvKKrfG4Oa7CpS9SiS7uGbVax8+pqtqS8Mx09O+2VBj2gpdyMuw2riZ9G79YfVKtorBQ1kQkppmyMPBzTkLbC4U1ZCYq+FsgcME41x9/tWZuGxdG+V09gr5KCY67rCWg+zgtfH6vx22nHdQ/SslJyx/7FTJsk12sciR/E+Ti17VNkptsrZnfhp7lGPrDsuPu0SBtVVUxxcbJXQnm5g3wtSGZVP7ZI5u3peVQ/qgyONkqjHFpQOyc45MVhDtvaHaSSSxH9OPCnR7UWiUaV0Xtype9P4KzjbHzso2bLTg6tapDNmJvst9yvY75bD/AI9T/wBZSortb3cK2n9rwEu18Cd1nyzPt2VlP1Ge5PM2Ul+yz3LTw3O3AjeuFGB4zNCmNu9lYMyXi2s86hp+Sa5JBqyXyZSPZOQ6YHsUmPYsv9b5LUx7RbNMwXXqGQ/Zp4nyn4BOHaq2vG7bbTeLg/gC5jYGe92vwUMsmMfLJYYl9niLKSk2Jpxjfy7Kk3jZ2z2WkbNd5GUjHaRsI3ppT3MjGrj8FYOl2zufZttHT2aF+m9GzrJcf6R/D2NVrs70diKpdWXad9TVv9eV7y+R3m86+wYCq25+vs5NOjo0vN77V/k5xSbP1d/rGtjon09vY4OjpCcueeTpnDTyaNAuhw7OTUVK3LQ6Tme5dCpLfT0kQjp4msa3uCptsLvDYrWamWJ0pc4Rsjbxc48Asm9Tvl3WPbOhxMiGNFVY8dL/ACzC1Ebo3EEEYVjZLhJT1EYLjjIUamuDbpXmgrKKS33FzS+ON7g5soHEAjn4IjEY5McCFUlCVEls2q8irLqaXJL2kuH5O2g2kc3TeiZKD5xAZ+C4daNqJ5618NwnkknY4td1hySBzC6ztk8VMlfNnWSnpWe9kn/CuB1lCXXCUPyHO7bXN0IPBb86P3VKWzjsbOfS8qU9b55O37NQQ1gE/WNkj+yFr/yN6ZHiGJrO44Xn/ZjaWsstbG2Zw3wcAn1ZR+/JeldhtoaK+25ktOQ2UDtxE6tKxf2zrl2TOqv6j69ayKHtf8FJH6fYKlpBduZ58D4Jva7Zak2ztr7jao2Q3uMdtvAT/ou/S7ne9azavq32t+8O0Bkd6w2zF5fQ3Zjiew47rx4KWjIliWrT4KV2FHqmPKco/Ujjj43RzOZK1zHNduuDhggjiCp93p6Cnryy11MlTSgDEkke4c410W76bLC2hvkF2pmAQXBpc7HKUcT7Rg+9c3AxqF2VNnqxU0eX5VDoscGdF6PbRYq6218t3qxDURtBibvAZ0445+Se2XY1m09s3PV9Kjx/WCwVJKWOGCcLa7H1Iff7U3/vMQ/2gpe1pSbflGVkP7dI6NdXbSUlfczaaCSaCaZzmu6rewdRvN/bkKt2Wpr/ABXdjrnSTRwFrwXSQMaPVPMDKotuJ3C/V4D3ACZ2mT3lStgaWp/LUUskUzYix433tIactONSqfpONfdxyP8AU7lpb4NDstbqSosNNJK2bfc6TJZUysHrnk1wCtmWag6xmW1WN4f45P3/AK6pdmXXGOy07YKejdGHSbpknc0ntniAwge9WfXXjI3KW2B+eyXVUhAPiOrXE5cZevLn3O2xGvRj/Qe2MeI9mLewE4a14BJycdY7mrsSrNbKfRbN21pOXdSC497iSSfeSrYSqnKL7iyvBGvUMVferNBUb/VtFTNhkjmEkMaBq0g47XDKkfkO3/Zqf/OT/wDGq69unbJbqmi6v0qKpEYbISGPZIN1zXEZI4AggcQFJFReP+p27/zcn/8ArUqhJpaGbSZDu9HT0d62dNOJgXVmDvzySaYHJzilV1VTv9Ma6gD3NkcDmR/a18FHurq5972dNXBSxs9M06mZzyTpxy0YCWye5GvrmOqKjqxId0dvQZ5aLoKIv9tHZWxHvLkvwZquqqPJa6xtd/48oWdmulpgldH/ABZhBB03qyYZ8Vr7jWV0T3B13midjO64vB+SzVfcY6+sNtvdZ1jXjepq52Sad/DDsgExnn3cRzUuN55XBN1KDlXtexZVb7QaW3SWa1UVS+oxGad0krpg/AJ0DuGSRqNUijuTKW5Np6iw0lPMNC0mUOGRpoXLK1VJPb6t9PUsdFPGdRn3EEcQeIIWph2ojrKikkuNooqmpjayM1Dnva5wHDIBwtCVLjHj6kc9RcvVTfD2WlRtNSWWseZLHTPFTGMuY7tOwcbp389nXkkbBVIdUVxbDFGH0s7sNB7PZJwPDkn9ob7RUtIA6w0MolDowST2cjvIPwwdOKj7A1MMgqIm0UUcjaKbMoe4l3Y5gnCZRDUJPtJurPVqOJXsgT5I56hPbcbQ2y726209vtbKKSmi3JXt4yHv/fvTd6ZvPOBlZutge05cCFasbXgbVXGXa35RVynimmTOieHN0IKclGMqK9Vt65JppPhk24XqsrIWxTyuexgwASqd5S3nVNOSTk5eRsIRgtRQlEEOaAUbHgQQQHFIhQwjRDijSoBTU41NBOsQx8R9nFSouSis4qVEo2y5UifByXVej5nV7LyvOhlqXa/qgBcpgPBdb2VHVbIW4cOsL3n2vP4KtbLwjoemw+pv4RjbrU9Zeq1+eMzh7jj7lNtlaWTMIPDJ+CzMk5fUSvJ9Z7ne8qZRTHrOPJdPXPtgjgb6lZa9+7NxaKovrHkn1WYPtIWip3dY9jftED4rF2F5dJUPzzaPmtfZyX1sA49oFc5mX91rPUuk4yqxFpD3SFP9DHGDpkD5lZqaocbXbrjFg1NE4AtzqTCd5vsMZx7FY9IM2auNhPM6eQAUPYaaGS5voqpjXxSt32B2o32g/cXLTwJfw0ch+pYd0uPY7J0N10cbrrZ2P3oo3ipp/GJ4BGP6JYrnpIow6CmrWjO4erefA6j45965V0e3A2TaW2GV5DIZX2qcn7Od6M/1Hj+ou/XWhZcbfNSTaMkGMjiDyPvUNj9G9SOZlH1qXE5Zabqy3sJFHHJO3e3JN8tOowQ4DRwTJulY5jGdcWtYxjOzoSGatJ8RnirOr2RulK2aRzYnwxNLi9r+IAzw45TWzNkdeK0MOW07O1K8cvAeJWj3Y2nb5MtQvbVb4KN+XOc52SScknme9SaK3Vda7FLTTTeLWkj38F1ah2btVFgx0jHPH15O2firUMDWgNaA0cgFVl1PXFcS9Dpbl98jmdHsTcZyDUuip2/pO3j7h+K0du2Lt8ABqnS1Lu4ndb7gtUQiOnFU7M22zyy5XgVV862NwwxwQtigY2ONowGtGAFn+kO0flvY+50TWh0roS+Mfpt7Q+WPar91RE04L25804TkAtwQoIycWmTSitaPF10Lrhbo3nJmj9bOhOgwfgqenu09BTzxRvLWStLXDvHNbnpG2fls2015ipOwaeUTRtHB0Eh4ewuHxWDFmuF3uMMLIvR2ySNjMjxho3nAZ14nXguhtvrlWpFbCx7fUaitmz9Om/iRaIpHZY4ySMH6Jf8AsKraurp6agjdvAzu1wnOkW6UlDcG26iAFLRRimiHg3TJ92SsFK6rukE8kZ3aeIdt+cF3gPDxXLW4ssi1tLg9Lp6rX07EipP6vgfut7lrXOghcWxjR8g09g/FLsNYKGqie04DSOCpxuxwYYBgfBNtqN1w1Oi0sbHhTHSXJyHUs67Ns77Gdb6TtqI6vZO326meDJUODpMchwCpNk4gLbcajgGBjB7XtC51JWPqaqPecSGcPBdR2fhMPR/XVLhgvqIWj+uFY7ONmdGfZx8l9RPDbDZN71W0Tfi95UG6dZW2qspqOYRVTyx8bid0HdJy3PLIOh7wE492NmLOW8fRmfemoYXBgeQcHXK5q5Sja5R9j1bFhC3CjCXhoo7Fb7nRyvnuErGZaA2Fjgd4tzuk40ABJOOJOFbR9loHDCdmOBrwUYO1VTJundLcy90zCqwq+ykkhydZK4cCorXJxrlVNNMsYK2aL1JHN8ipbbpM4YkEcg/TaCqYO0S2vRtoR0wn5Ravmo59Ki3U0g8k06gsUvr2an9gH4KMx2ida5PVs14ZUnhUvzEcFi2bedbPF7APwTsezOzbyMWuMeYH4JuN+qmwyYHFOWRZ8lafT6vaJMotkNnnkYtkA82j8FoqDYyxtxuUEA8mqnoJyHDVau11QIGSrNdjl5Zk5VHpfaidRbPWyEDcpIf6quoKSnhGI4mNHcAAo1PKC0aqWx471ZUUY1kpb5Y8GtA0GEYwEkOQJTivyKyqDbOxDaGxzUYf1cwIkhf9l41BV3lJLgjxyKkcvgjv0tzoG3Ky01KaR2X1ofvGTHMdw46eSduEm/VSuaMNyT5LX3+TELsLNxQtkppXEZPeochyvlpmx0yqFEdpeTJX2Uuoax5Pq+hj/fhcvvjBCY5MDR5b7D+0LpV61tdxGdc0o/2plzXaIl9LK0esG73tGv3LewIv0InKdY0smxfkhQNp6gmGpZvRO4gcQe8Hv8VdW6uuux9RBXRTOfROcGx1Q4H9CTuPwKx8VSchwPitLadoXxUslLOyOopZBuyRSDLXA8cqXIxo3x0/JRwuoW4U+6Pj3R2KDbBm0dqG48R1LR2488fEd4UCaONmJoXZxqR3Lj1QTYK+OW3TySULu0G57cB7s82rc2LaGnuFNuvkayZ39Vyw78WVcXGS3+T0LpXUsfJhqt6fwdR6Q4m3XotjqTrJTSRPHkTun+8FxqjtlVWRzSU0L3xwt3pHAZDB3k8l2XaCoZH0OzjLT1vVsbrxJe0/cVxiCuqaaOaOCaSNkoxI1riA4dxXQdLb9Hk82/Uce3JfaG2nfHqd3A7nLV7EtP8AGK1HBx6VF/eCx7HOLskrf7D3SQ19pojFFuelxnfx2vW71qy+1/0OVu7lovNsJLdTXutlcyeoqRO47kjWtiDsnjrlwHdplL2ac+ivlLVXaq3aiU5dE8kva1wxvO5N0Ocd3JDa2qpKG/1c0EMk1aJXFrpgOridk6hv1iOWdPBR7FaIKy01V1utc+BznP6tz3hpeQMl+ur9cDAVGWlBOXgnqTntLyaayVLLcJbVXubBUU8j93rDuiRpJILSdDxVtHWU2+0+lU+hB/Ot7/NYq0bQSVUEVJcaSmrWRsJYZgd5oDScZB1GifjutvfSvl/IdCA17WYG9rkE9/gsq7o6nY5fJqVdXnVBQ14L6wz00djoWuqYAWxAHMre8+Knel0v/Wqf+1b+KoLZVUFZW01ObNRN65wbnDtM+1RJ6+gjJH5Eoc5I4O/FR/6JFvXuP/1uet9poLhVUx9DxUwaVcRP0rfHxViyrpif+kwf2rfxWONZQC2OrPyNQ9mcQ7uDrlpOePgnoLhbustjXWaiBrAM6Hs5kLe/wQ+jxSHR6vZJ/aX8skdwvlu6h4fBb3uqaiZpyxuANM8M6fFZyhqqWpu9TI3rjvv3jqNMnloma29VNyqGWehZDSwyS9UGRjdaTvYGeZTNJbZbTfBDJK2RssYkY4DdyMkHTlqCrTx41V+m37cFvptsrMn1Je5OughL5Kad7uo3yI5SMugPj3tPP3jVYDaellpLgyOdu69oI45BGhBB5gjgV0C+5guD37u+x7QXsJwHDCzNyfS1tK2jq5fR2xvPok8mvVZ13HkD1T38j5lQY3dVPfsbfUYd1EkiBarvBJb46S70jqyKAkQPZL1csTfsb2DlnPBGnJToqux77d22XBuD/wBeb/wKJSbPyCN2LnZjrnStb+Cs7ns2+1QUkxqYp+v4BnDgDlp5t14rT/gt6T8nGydkH3NeDRXoWWt2Um3YXtrGjfjyS54dkYO9gDdwTlNbKUYtNmuF4r3CGlNPJDGDxlc4YAb3qytdsp4rNJcrxltvjjzuj1pccguabdbYT3mbGkNLEN2GBvqxt/HxUNMHFOCfGy/nR9ecXH4MwZoY7jG6oAdG1w3h3jmp/SpdNnbgKT+L1IacNjxLkYyf35rF1tSS4nOveqipmLjxOVLKxMP2vKe/BEnOpwob0/K7KjPKrtkrQy9NHinHlNHimMAkYRHigmABAcUEBxQhQwjQCCVAKanGcU23gnG8UjJIj7FJiUZikxKKTL1PknQcl122EQ7JWrOmKbf9+SuPxndaT4LrlQ7qtmqRvJtA3/dqna/qivydJ05fRY/wzlTH5AJ44U6hf9IfZ81WMPZb5BTaA5kPsXSb+k4auPdav6mx2cOYpnd8nyAW22eGbjD4ZPwWH2dP8jJ75D9y3GzOte09zSfkuUyJ/wARnrOLDtxY/wBCi2+kDrq1o5B3979irbJSV0DoLu1ghpIZh/KJTuse4cWt5uOO4Fa23WaK+7W1MtY3fobfSOqp4+HWEE7rM/pHj4ArAbZbTzXisoomuLKamgaxsbT2d46uIA0GSeHcAFu4MvpSRwXXnuySRvJKaS4ur7jSFvU1IiMTBnJmjd2dcY1a5w9y9DbKXNt42doK1py6SMb/AIPGjgfaCvJ+yW1DqCiqaKdrZYJ24w76p7wvQfRBdOvpaqglcOtZHFU4xgjfaN74gH+kpc2G495zFH0z7ToE0YmhfE/O69pafIhMWe2wWuiZTUjSGN4uOpce8nvUmaURR754jgFVVde9kb5JJGxRNaXOdwAA1JJ7lnLbWkXNLfd7ly4taMucB5lMvrIW8C53ksJetr4qOK1m2Us15qboHOo4qZ7W9axrd5z952gAHvVBtHtfd32KLaCxy0VFY2URqXPro96Saff3fRsZ7J0IyM6pyqfuO7zqUtbI782wN+KzFPtVabnc5bfSXWCqq42OkkZE4uDA065cOyMd2Vz/AKQ9p2Ut/wBm7lHWMhNFTxV/o/XZE3WyBj2DHrFrN8+wpmWqbs9UuFm2kpquhrK9jxZRAGukgqnHtAkbznDJII0AGCpI1peSKU9nRNmb02+0Dq2GnlgpXPIgdIW5mj5SBo1a064B4jVai2Sesw8tQuJ7F7MV1i2otNNDa6uGppJamO4XA5MFXTEfRYOdXDs4bjTBXZKAkVMY9/uSWRSXAiZznpttTBcbVcyAIqhr7dUO7g8EsPsOfcuA0slabnDJKJaipp52iOFziSZA4aAeYwvWfSRaTfNjblSsbmZsfXRY477O0Me4j2rg9sdBTU814p2k3CqDeqkPqwFwIkcP0iQcHlnvKuYsoyr1L2FhKyMn6X9TBbZbLy1FxcJp965uJlqWxn6GAk6Mz9Zw5nhnRZd1vutPDOI2OqIGj6QxDkO8d3kuhXDQ+jwZLnHU8yVrdm7fDaLd6VWYYGgucXaKSSVfgHdK3mx7POL6jXTgnX7ph3x3Kw29qqKt2hqau3U7KeGR5JZGMNz9rHLKpJnFlKcZA8Uzet7HcvQ5bhvzE44uwu5T0ppeiNjiMF08Tz/XC4rs7HvzxDHFy9FbZ0gg6LWRgY6tsTj/AFgnb+ggsf1pGSpnme02GEc6SM4960lXTdTSNZjUBZvZlnXOsjXahtG06eDnBaraF/V0krm8Q0n4LKjV3dzPRVkuuqqK+NnNr5tNTUs74YmumLDhxDgGg92TxUCj2qppZGtmjdE0nG/vBzR544LdfwabVbbxf75LdKCmrX09NE6IVEYkawved4gHTOBxWo/hK7PWej2Pt1wo7XR0tYK9sBlp4WxlzDG8lp3QMjIHFJLBob7GufkxV+ps1Wdya18HP56mKkpnVE792NoznjnuA81QSbXwteQ2lO7y35Q0+5Q9oJ3nZmzgn1mgn2N0Xqjos2ZsLejjZ6R1lt0ktRQxTSySUzHuke4ZJJIJOpVejBqjDusW+TT6t+osqFqhQ9LSf9zzYNqqU0+91M3W8OrGPfvcE3DtfGX4NJpw7MwJ9y0t9sVqH8In8ix0MMdqku1PG6lY3Ee65rHObjkCSdPFeo6jZTZ2ppZKWosNqfA9u6WClY3TzAyFNLDxoa3Hz+TL/wCp+oy8SS1+Dy9bK+nr6fradxIBwQ4YLT4py4V8Fvp+tqHEAnDWgZLj3BV+3Fhk6OekGahBkda6gCWne4534XHTJ5uYdD5Z5pvZy0T7f7e0lppXObRgnrJW8I4Gntv8zwHiQqn+mJ27X2ef/wCjd/6r/wDQ97/7vjX/ANkU7ZwteQKX+tM0H5K0ptq6M0/WOimEucdUNfbvcML1RR7JbO0FIympbFbGQxt3QDSscceJIyT4leaLvZ7bB0/CzMo4m2t12hjNOBhm64NcW47sk6dytwwsaf8ALrRz7/UvUIeZJ7/BFpttYg8YpMj9GYZ+S2do2kopKA1om3IGaSb3Fp7iO/y4rtO1Wzdjl2Zukb7Rbw30WQjcp2NIIYSCCBkEEBeSNlLZcdoLnS2m1tdJPUlriCey3A1e7uABP7lOjg0WrcV26Ej+ocmDat+rZ1AdJcERxFQOcwcDJOGE+zBU6l6T6V8TzNbp2vA7AZK17XeBOmPius7M7GWDZ2xQ0voVJOYWb01VURNLpDjtPcSNB4cAFwfa25WnaXpDoG2iip4bUamGm+iYGCob1g3nkDkc4Hh5qWuqmXCjwjPs6hkJ9zl5NFT9KULn7ptmR3CqGfktts9fqK/0r5aMua+PAkhfo5meHmPFbM7N2QxGI2i39Xgt3fRmcOGOC4be4X9HW37dwPNrnG8zOu9C46jxLD8h3qP0q7VqC0x9WbbCSdj2jod8u9JZ6I1FY44J3WMYMuee4LEy9JEXWEfk4gDvqAD8lCqXzbc7b09vonk0ocY2vHBsY1fJ7eX9Fdwp9lrFTUzIIbTQ9Wxu72oGuJ8yRknxQqq60lNbYtubZKb9N6SORN2jpb3TSiJr4Z2t3jE/Go7wRxT9uAfQy+Sy209PDbOk2uo6KNsNMyctYxvBodGCQPDJK1FocBSPzwwq9tMYXLt8NHS9KypX425eUzB3jPoVxH+cpv8A/qVz28sDJXh3Aj4Lotzdlle0DTrYB/syn71kdrbY6OhZVsB3SMFa+DpUo5jq895szmEO6wujecOa4t+KsesZFE0jiVSVznR3RxHqvIdj9/FOVkzt5ufYPFSqfLKEoLRpLdV076iNta/EGRv89Fo3bIXVs7rnbbZUUtrkO+xk+hcO8N4j2rG2ItpqqKd+DM1wcM6hp8PFenthtooNp7QI53D0yJuHjOp8UWvceVwFNkqZd1b0zm99qa+k2et9vmwaCQ+kRSMcXMe7GCPAtJOQdQfBZ2j6k1MYqd7qN4b+7xA548V1K/2qCidNQ1zT+Rqx+S5uppJuUjfDvHMady5lerXU2e5y0VWB1jNWvactkafVc08wQp8ZRjHtiU862zIm52Pks7420MrWCxyTyU+NTMMHKsNlqtlFdqKpkGWQzMkIHcDqsxRQz1EwipoZZpPsxsLj7gtladk75LuudR9QDzmkaz4ZyrqcdNSZjWVtLg3u1NqpH3iSsrZJH0M308XVDPX513Q7g3zWVrjU3OqEs7A0NAZHEwYZE0cGtHILa7OUl6t9GKSrdbqmjGvUzOLt3yIGiuGxRMILLPbXZ5tkIHxaqcbFU/q514I412z+mtHO6OH0OOUMjDql7C3fP82CMEAd5HPlyV7LaTBHDRRNOHCOaV54vcW5AHcBkhaeV5jc5x2chk/SieH/AA4p1m0lEajdqbYyKXAGJBg6eYSO1yl3RiLKuda7bOP9mQtnrA5lypJS04jc13uUS6bOuilJLTqSt3bLzRPe3diYzPDCbr7tSSztibEx7nczrhQK+1WN9pI6q5VcT5OfVFncNnJWAHPpbXY/oFQzbZI5Nn3EEBoHH/TEroldcKahidHUUsT2HtjAx4feqiXaO3vfTBtBEQNG5PqjJ/8AdOU5z8RFUlW0u7k5lW0Un5RqHNyPpnEEH9IrT2Ketnpqtlc91QG7kjHy9pzDvAHDjqARyTEd9oLhfJI2vjpoScndaOPmdVbUm0tvt1wmoXU8FYXFu486E5PB2NNCOPin5Ee+Cj28mhg32VzU98DV/pzLIwjUmNuixN9oH9T6pGH/AHK82g23gl2gpoZGej0JAL44+z2eWTxPf5FSW7UWb8p3FlPTw11NHTdcI5XEtDxjOCdRplQQplVqTRr3dU/cVuMUYuioniV3ZPL5Lc2Ky09LR/lS9nq6CL1Gn1pnfZHgqxm3VpbI/c2dpAW4/nTj5LM7UbX1d7qRJOWsiZ2YoWaMjHh+Kty7p8a0jmmpSk9m32lvDrzaJ3gCKI07+ribwYMHh7lwKuqt4HJ8V1a0zmazMaT60Lx81xioflvsWX63bKUEd+8OMcaqevKIs0m85WNyt1ri2Zpa2G49ZcpJHNlpNz820cDnxVJM/CiyyOPMpY2JeTOur34YzI5RnlOSFMu1KE9laSEE5KSeKUfDVEUMjQg8UEDxQTWKBAIIBKAYRoBBCAUE4wapAS2cQkZJElRRuIyAThPRhaPZe/2+22e4U1Vb46ieoZuxyO/mys8XBz3EcCU22MUk0y5jtt6aH2+qe/C6xdju2CIDlQj/AHa5M06HHcuq3U5ssX+pD/drPtf1x/qdV01bqt/+LOWtPZb5BTLee272KA09lvkFLoD9KR4D5roW/pOGpX8Vf1Nrs+f5Cz9Z3zW22YP8rce6M/MLC2B38hZ+s75rbbLnNU//AEZ+YXJXv+Iz1uhf+mj/AEI8F5dQHaCGIkTzQQuBHHdBcD/eC5PUsdE6Tf3W4PZzzHmtbtLJJFeS+JxY7qwMg4yDnIWdrbTcL1XRwW6I1crm7zYoYyCAOJfyGO8nGNV0OHNRrSZ551miX7mc14K+31UjqjERbluvrccLuvQ/fXQ3ix1UzyRNv26ocTxPrMJ9jh/VXGv4rVVpZDUV8sUYlGYw1+c/joRr4ronR8KJ72UPWgvfI2VnEYe0ENOQcjGStCerK2jmrIuE9nqqtbvU7xzHaVBcrfS3OjdS3CET0r3Nc+JxID905wccRpw4HmntkNoGX2nqGSR9VW0r+qqIic4PIjwKlzwPje4bpPcQsdJxemWE1JbOX2asqbJsbtJb6KF9Tc7DPPTUsbGb7y153oSBx4P5fZStmqS//wAUaK2263R2v0LcAbeWNmFZnJeXMbrGd47w5ngulR0D99z2sawvILnYALvE8zopUVua3V7yfBownuxCKJi9n9jbdQbMNtVfDT1j3xSQzTCIMLmyOLnMYeLWguOADotBTWWmZ6IYaKJz6SMRQSyNDnxtAxgPdrw8VfxwRx43GNHjzTpKjdjY9LRXx0LzrI8N8tSpMUDIvUHtKdygm7YMS7gdMrz1crS22bQ3qyyAiBs5kiHdFLqMeRA969DFcn6Y6D0a8Wi7s7LJ80M7h46xk+35Kal8uPyLRaqrozfj3OY7O00L9oKilqjieLJ7RzvgccLO9KG1PXF9BRvxBHo4g8SlbbyS092FVTudE+RgeHDiHcCFzK5VD6iUk5LnFaaXdFTYmVWqr5QXgqZxJUziOMOc9xwAOJK00liH5I6t7nOqGsyQAME9wT9ktQpGiaYA1Dv9kd3mtdsnR+n3yCnIyCyV3ujcU+NHDlIpTydSUYHOtnj1ddC48A4LuO3d7in2MdStcN50bSMHuwfuXCInGmqMc2nBV3LdZassZI926BuAeGFHpa0TOLnJSN/sFKJnURGu5AWj+u5aTal+KCYDjuO+RWE6LqgvqWMJ9XeA/rEra7UuPoco45ace4qlXHUH/U7LubUP/iMfwUAfyxtL/qtP/vHLZfwoTjo9t/8A+UZ/upFj/wCCk4C9bStz2jSQHHlIVrP4ULXydHdE5jSQy6Rl2OWY5APimy/7py55+vfa2bshH2f/AEr2N0YNx0abL/8A4yD+6vGd1nYdnLMwPaXtYcgHJGBjVezejNrmdHGy7HgtcLZBkH9QFQ61Wk/lmh1GanftP2X/AAcD2g7H8KiHxvNL/u2L1SZBugkgLyxtIN7+FNCR/wBsUo//AIbF6O2ujL9j740EgmgqMEcQerdqPFOt/l/oZ0Pcy3TjsaNr9jJn0sW/draHVNLgavAHbj/pAaeICh/wf9ijs1sq25V0Zbdrs1sz2uGHRQ8Y2eB13j4kdysehHbP+OWw9JUVModdaNraatHMvAG6/wAnDXzyp3S1ti3YzYusro3tFwm/k9G085XA9ryaMu9g70zunr0xdRf1G2aQWZBBHIg5XlfaR2P4TkYH/bNN/dYvQ/RvvHo92bLnFzzboHOcTkklgJJ8dV532kGP4TjP/wA1Tf3WJ9C05L8Mba+EeoL1G+eyV8UTC+WSnla1o4ucWEALJdEOwEOxlhY+qDJL1Usb6VKNdzTSJp+yPide5bgnCh2670FwqK2Chq4aiail6ipZG7JifgHdd3HBUG3rSJdLe2cN6dOkQ1lRNstYZC6Frtyumi/nHZ/MtI5A+t3nTvWB2cp5KLa6yQTkdYKunc4Dll4OFtenLYg2G6t2ossfV0VRKDUMYNIZyfWA+y88f0vNYq117a7bWx1DW7hdVUoc3ucHjPsV6r7Pp8a5/qMah2tyf1bWv6HsR5wCScBYnpU2W/jRszI2maDcaXM9MftHGrP6Q+OFqbyN+01zeRgkH+yVh+g7ax20uyEMNbJv3O3tbBOSdZG47EntAwfEFUY7j9a9h8mm+1jXQlsw6z2E3SticyvuDQ4NeMOjh+q0jkT6x9g5LpQcC0LL9Iu00eymy9Vcey6pP0VNGfryu9X2DUnwCb6MZJZej+wy1D3STSUrXve45LnEkknzJSz7p/W/cI6T7UcX24G90t3H/WB/ugramqWwUrg440VFtxLjpcug7qkf7pqKunJhIB5Kvn2enKL/AAdf+mavUpkn8lFcKoH0450NRG33Q5/9Sj3usjm2WkjI7QxhV11mLaWQB3r1svubHG1Z+puDzE6Ek4W1hrdMTler/wDuptfJQUVDHPNLNOxzurduDHDvULaeh6qojqIA51Pu7ucY3XeP3LcWi2f4G11du8K2MZ8N0j5kKtlYySJ0UrA+N4w5p5hW/RU48GR+5lGen4MjRT74APrhazZLaCotFfFUU8ha9p1APEdxWNuNJJbK3dBLonasfjiO7zUinqMgOGh5hVk9PtZbaT5R61tVdR7XWESMDXFzcPZzBXNto7hQwMjtVbGa99DN9FNHJulsX1oieYz3cFzS17V1ttjfBR1D4WyDEm4cZHcm47o98hc7UnVPrXb4I5RUmtnYrftrSU1K2ChpIqOMD1I24B8zxPtUuPa+aZ7I4G5e84aGjUk8lyiCvaW6jGVfbO1O7I6can1R5c/fw8spJZHpQcpexbr6ZDNtjVX5Z162VkjnZq6jePPc1HkO/wA1qC5kFH6TVvbTxcmuPa9p+4Lm2zNW0zyVNS4mGAb58e7HiSsztXtZcL9djRUBIkGASOEY+yPHvKya8meTM6q/pdHTK9RXC8/LZ0yu2yttI8tMjRjTL3aqxtN9pr1T5fG2Wm4ZkaS0n9HOufJc4smzVvtMTKi5EV9e/VsbjlrfE962VudUOLX9STyGeyGjuA5Ba8MeKW9nH5vVpS3Wq1ov2UMEBnnikmaxrS9kZOd0gE8eYWJk2idHc2u3sYK1hmLIJDUSNZGGu38fZxr8Fwm4Vs0dye2Bsk8Wm69jScjlnHA8MhWqXFb72c3HFna/oj/Y6pfdpRPVW/1XMc7cc12oIOmqRta6np7DNWQjq6iAadWdHhxwcjkcnK51RvrK6to2yxvihErd6WUFjWjIyclaLb682iCgkoIiZJJ2lokfIezpkaHTU66pe6H8j8Fj9nbGa9Ra2YGG5OfM95cck8VNtl3jiukbqtx9H06wjiGgg5HjoslRmo1+je5v2mAkJ+t9IpaR8z4HiOUdUC8Yzvcx7AUyWTHXk0o4Fi9nocqr2+43Opqjhoc7LWg6NHAAeQAV3snVu664yZ4UcrdOPaGPvWOpLXM5oEMjSDqCRx/fuWuZQNs9llc2cTzVMG88tIw0ZPZVK3NUVz5NXD6NOcuPtQtkrmVE7C7JAHBNSyk81V0ExfNL5N+9TC5Wo2OS2Zd1ShY4o3uzUhNpp882uHxKyOyWzdFfKWufW3WnoXU7C5olP5wjkFqdlf8A9Kpj4P8AmVyaSR7Cd12NSsFWL157O7yqpPBpUXp6IdewRzyNacgHAKr5OKlzHOc8VEfxKlT2+DDtWvIy8psapb03lTRKEzpvRl0ZzbbUNZUQ1MUAgwO2Cck8P/dc+vlCbfcZqYneMbi0kd4U6zbS3C0xSMoKqaBsgw8RvLd4dxwqeqndUSufIcuOpKszlHt0Z9cLVY3J8EdAoFBVmWwIBBAIAUEEQRpUAoJbUgJbUjJIj7CpEaisUmNQyL9JKj4O8l1Sp+kslEft0bR/sLlcS6lSuD7BaTxzTtb8MKjfw4v8nVdI5jZH8M5Ww9hnkFLoD9P5t+8KG0bvZ+ycKTRHFQzxyugXMThI/Tb/ALmzsJ/keO57gtrsq7+Xkd8Z+YWFsTvoHj9M/ILZ7LP/AOdGeLXBcnk8WM9axH3YsX+DM7VsP5XAHEsA+JC6Bc5aLZLoxmpKF7fypX0xfNKPXw7QN8gOXeVgts8surSNOwdfJxVbc7k+ua3rXANxgZ4eIW/hJSgtnB9ejL1JdvyZ6pqZqieN75HubuDGTw5EeGoVrZ6mSnnjkhkcx7TkEFU9XPT0bd0ASguzjhj2qJS1j3zZ4NzoAdAFqVajwc3lLv8AqR6q6BKt1VWXWaonLqmVjHbpOpAJ7RXZQvMvRFehR7Q2Sqcd2OpYaCbPe3G6fc5n9Ur0yOCzsyOrN/JXofGg9MoIkaq6LKYaJF7UaBdgRFDKIlAxyBlZjpHtH5a2NuNM0Zmazroscd9naGPcQtKUh2DxGU6L7WmiKTPIO18npYoaluD1sW+fA57Q94KxtPajBcJ5JgDuPIYPvXT9u7IbfdLpbwMCiq+ti8YZcY9zt33lY2u1qJj3vPzXRUxjKKaK1+Q5vb8kEcVt+iGESbaQlwyGQSu+AH3rEHQlbvobP+F7v9Vf82p13EGVo+Uc06TbE+wbWV1MWFkZlc6PuLScjCzlPLiVh7nBd1/hF25r5oKkN7QbjK4Jwd4rNUuTZp+zZvujJwjvb4zykcPkugbTHMDlzHYqo6naIOzgPcx3vaunXv6WmfzUUY8SR1FElKNT/BjehjaKHZLpM6uveIaKtY6ikkccNYXOBjcT3bwAz+kvU20FkoNpLJV2q7wmSiqW7r2g7rmkHLXNPJwIBBXjXaK1Gqf10IHXNGC0/XH4rW7GdNO0Wy9JHb7jDHdaWEBkbapzmTRtHISDOR3bwOO9Vt+rynyZOdhWYtj2vpfhnRbb/B3tUFzZLX3yqrKBr940op2xOkH2XPDjp34A9i7TWVlHZ7ZNVVkkVLQUkRfI7g2ONo5ewYA8gvP0n8JHsfRbMHrP85Xdn4MyufbadIW03SERR1DmQ28PDhR0rS2LI4F7jkux4+wIlGXmb0ipVXKyXbWttkrZS+P2j6dLVd5Guaa69smDD9Vpd2R7AAvXe1ZA2VvQ/wC41H+6cvDkDqrZG+2u6Ubmyy0krKiNz2nc6xpyWnwK6hfv4Q10utlq6CCwUVLJUwvhdN6Q+TdDgWkhuBrg8ynyXralXyhbaZ40nXatMwPRhtxXbC3xtxoo21EE0AiqKV79xsrcZGuDgg6g47xzUzpP6QK7b6609TVQMo6WliMcFLHIXhhPrOJIGScDloAAo+xlvifbpX1MEUkb3AMDwHaNGMp/aa0sdbmPoaZjTE4uc2JgyWka+eFHLNqWR6bXPyasP0/dPC/dxlxrevc9d9Gbs9HezGf+zKf/AHYXn3aggfwmox/+80v91ia2S6ebps/s3Q2mWyUVYKKFsEcxnfGSxow3eABGQOYXP7jtdca/bl21UjIY7h6WysaxoO41zMbrcHUjDQFPXTNSk2vkwZzTSR7hv0kkFmuEkDyyVlNK5jhxaQwkEe1eO+iXbWfYzaeKvndJJQVbRHcG5JLmk56zxc0knxyRzW6uv8ISvuFmqqSKwUsE88TouuNS57W7wwSG7ozx71zW1WGSsssk7NJxjqGk+sBxz58vJMhFVRfqryWKqZ5U+2n25Pa9ZTUN8sslPUNjq7fWw4IGrZGOGhB8iCCvKdZs3U7I9KVstNUS+MV9PJTzH+diMo3XeemD4gp3YPpjvGyVljtD6GnuNLASIevkdG+JufUyAcgHhnhwUTbfpMr9rLpaK51so6GW2SdbC6NzpHOO8HYcTjLctGmPanVU2QbS8MgslF+fKPXd0H/Ndb/oZP7pXj7YPaus2QvUFyomtlBj6qaB7iGyxnXGeRBwQeXtW7ren25Vdqmp2WWihnljLDKZ3Oa0kYyG4HfwysVsbbo30c0tbAyRkm62MSszoB63xUPd+1rk7V5L+HhT6hcq6v7kvpD28q9tblTyzQtpKSmaRFTNk38E+s8nAydAOGg816O6L3B3R3s8Rzoo/kvOe09si/JLX0FNGx0L99zY2YLgRg+eNFcbK9M9fs7YKK0i1UlXHSs6qOV07mO3c6ZAB4Z4ojOOTUnUvAZmBZgXdlnO/cjdIUm50w3Vv/eW/wC5akVEmQBlUTbhV7S7U1l8rWsa6V5lfuAhodjda0eQx7vFWFVL1bC88GjKyOpzTsjFeyO3/S9Mq8SU5rW2ZO8VH8npTp231EvvlIH91ZqaTMucqyuUmYaNudW0zM+bsvP95Uz9ZW92V0+PHtrijgM2z1Lpv8s7LTWqOl6FJ5Qcuke2Ynx3guZu5rsNXFudCOO+Au/2guOZVqh8MxrfuI9bTR1lM6GXgdQ77J71jZ4paGofFKMOacHuK3ITk0tOyCCLqo/S5C4GZwBc2PgGN8zknnwChy4qMe9eS905O2fp70Vtz2YmslLC+4va2eaNsnV/ZBGcKvpXsyrTpCvUtxvEj3nADQ0DyGFk46pzeBUMp68D4we33GtL4mQggjK0Gz0uKJrhjXLvwXOBWufhpceK1tkqyKOJmoy3Cy+pTbq0jrf0rCCynJ+yNvX3RtDs9Kd7Ds7xHkNPiVj6G4OpYg6KQiRx3nO5uceJQ2pqj+Q36nl8wsyawljQOGii6Xwm2Xv1RbqxQXwdLtu0lTEN7f3z48VoINuag4YXAE6cFyCKvwzGce1Lhub46iN7XnLXAj2Fbkbt+TiLsaGto69tltJFBaKqkbVOnqiOrlLdGg5wQO8ZyM571y+lutRHOZWSkEHRQqWqlraV4ke5znEhx4nOSjFHMxrR2S3Gc7wxjmU31V4kOrxZRip0eS6n2mqHOg9MkMkLXjsZODrw8lnLrcJbhXvc8lz3OySVEdmsq2sheHMiOS4cCfwU1lIIi52W7x1OSBg/gmuxRel4JfSnem5PckWFNcpqaNrQ5heAO0R2veiv1fPVOpYJzksBe8Y4E+q32D5pNooHVANW52KVh7VQ5vYae5oOr3dw4Z9qurOyGovMDdx7494ndldvZABOvLKhuujFdyRcw8Wy9elKfn2EbPbO1VYI6qpZJBRk6OOQZQOQ8PFWO0ha2ina0ANDMDHIaaLoe1HYjo4/sQ/h+C5vtK/+SVHjgfELCnlTyLVvwdridOqwsWXb515KG3HD5T5fJTt7KgW8YEh/S+4KXnGSuor4gjzO/m5/1N9sqcWimJ/ybj8SuTS8/eusWM9VZIydN2lLv9krk7/VHkucg+62b/J6BnLsxqY/ghSjUqHJopsyhSK7FHMXjL+CaTj+CbKmRnzEZ0RIxwRJzIgiggeKCRgFzRpKMIAUEaII0qAMJbeKQOKWOKGPiPMT8ajsT7FDIvUsmRFdLsr9/Za2uznc3mH2OK5lEuh7LP63ZQt5xVDh78FUMn7dnV9Ce7XH5Rga1nVV1TH9mVw/2iip3bs8Z8VIv7OrvVYO9++PaAVCacEFb1b7oJnE5MPTvlH4ZsrE/SZvcWn4LY7Nybl1pz3kj4LDWOQekPHJzM+4/tWqtEvV19O7ukb81zObHVzPUOkyVmHH+gxt+3crmuH2ntPvB+9Y4TSRuJY7joRjIIW66RIvXf3Std7C3HzC5+88ccQtfp8k60cr16LjdtF9SbEVV9tjLxMYqOmklcxk00jsPaxpMjgOTWge06BZqkhp6eT6NxkI4OIxp5cl0XbO+R1Oyez1rouxTxUDW5bycR2vbnOVzukpn7+7ukOBxjC1K1p8nJTnK1b8s7BsbdLdHs5L1u6KmNzQ2PlIM/AjiCF6Xs1YK+1UtQ1wcXsG8R9oaH4rxXbKiClmaZsv3CC5jdNM8+5eluhm6mWlu1pml6yWkqTKxx+vHJqCPgfamZte4qaKEJds9M6VlGCkZyjyswsdwpBFlFlAuwyiJQJSSUIa2AlJQRpxG2cg6a7Y2O62y44DYqxjrfOeQJ1Yff8AJcLqWOa5zXgte0kEdxHH4r1N0p2sXXYa6Rj87DH6REe5zNflke1eYr5KJqv0howKiNk+PFw7XxBW506zur7X7FG9fUVD1t+hw42wx30z/wC81YZ5yVseieXqtsoNfWhkHwB+5T3/AGMK/KN3060YmtW8BkhuV5dnaWTOB0wvZfSPQtrrS9pGTuaLyRtJROpLg9hHAlZkPt2alctfSLsVRuV0LwfqNd/Vd+Dl2SZwlot4a7zcrh1owK6nBPGQxnyeMD44XXbDWCazR757YbghJB/W18nQ4bcqF+GZqvG5O4KBNFHOMTRseP0hlTbrIDVO81ADtVz2X9NjaO5xlGytKa2NMt1ICCKeL+qpNRWQ2+mLnDAzhjG4GT3BG0pOwmzr9vekOltb3vbQR70lQ5hwWwM9bHi4kNB8fBNxq5Xy+t8IqdVy6+mU91MUpPwWGyOw21fSK4zW+IU9ra4tNVOSyAEcm83keAPsXSqT+DbCIgKvaiXrcfzNC3d+Lsrt/W27Z+yF7+ooLVQQZOBuxwxNHLwHx8yuIXb+EhFHcHNs+zvX0IdhstTUmOSQd4aGkN8iSVrwc9dtfCPO7rJXTdlr22U20PQHtHY4nVmzdyiuhZqYmNME58gSWu8shcxrLzcZmi3zNdFOJOqkGDG8uzjdcOWvFet+jHpFtfSBb55KFklNW0xAqKSVwLmB3BwI0c04Iz36Fc9/hK7ExyUMe2NsjDKymfGyuwNJGbwDJD4tdgE8wR3JYtOf8Rckkcq+qDhXNpPyiFSfwbqt0EbqvaWminxlzI6Nzw09wcXjPngJz/8AlvnH/wDVMP8A5E//AOxORfwk2CBnpGy7zPgb5jrAGl3PGW5XZthNohtZsfbL6KY0npsZk6jf39zDi3G9gZ4dyWdl0PuK6jCXg4yz+DnLz2oi/wDIH/jWG6SejC4bDz2xrbhDXxXGXqInxxmIiTTDXDJ0OeOe9de6SOmhuxW1k1kdYX1vVQxS9cKoR53xnG7unh5rlW23SfJ0gXzZmEWz8nwUddHJgzdY57nSMHHAAAA+KfCVsuX4Eeo/bwzY0/8AB1rBG3r9pKZkuO01lG4gHngl4z54Upv8Hido02lhJ/1J3/GvQLiBvHuJXniP+EZUdcWy7Mw7geWncrTnAOObMKOF10/tYShCPkzu1PRLtPstE+40boLlTQgve+lB32NHEmNw1HfjKh7PX0XOMxyhrKpjd47vqvHePwXp3ZW/Um02z9FebdvimqmbzQ8YcwgkFrvEEELy70r2yLZTpWqIre3qqWcx1bI26BolyHtA7sgnwyob4/uoOM/K8Gv0fNlhXx7ftk9MuzOeRwoU9PTSO3n08JdnO8WDKbEvHVAyZXN98o8Jnqf7euzTkkxZw0BrQGtHIDAVVtFOY7XVFujjGQPM6ferEHJVDtLMNynj5PmGR4N7R+Q96XHi7Lor8kWfZHHxZyXGkZW7vDqyQN4NIYPJoA+5RKOA1FXHGNS5wGEiVxc8uPEnK03R7azcNoKYEdkPBXeLiJ4tY9ts7HtdB6D0SmDGMU2Me0LhJXoPpic2DYaWJpAyxjR7XtXnwqTG5i2Z9vkTlQ7pAZo2SRnErDoVLKJ2CCCMjuUk49y0LVNwkpGev8T3llS9p+kbkn9IaEKkIHetvSUkThJTTPPUSat3+Eb/AD7jwPsVDdbHLTSuDc6HgVRsqfk0IXRb4KZuAcgrSWWcmJoz6rtfbqqA0cgOCCrCgJpXNMn5t3Zce7uKzsmtyho3ukZHoXp+zNFd/p7ZJGe44WPpJetYIz67dFsHjrIHMPrY96yFxoZIqhz4gd7iQFVxn6bNTrUZX6sXtwWUdsmIDjoPE4TrKVkbsPlbnw1UGnvs3VtirIhIG6A53ThS2V1FMQGRSMkPLG9qtRXR1wc2sfu42KNPIyR0lL1zHHiWjIPsT7g6emMNTTVExI9bexjyAVzb4a5lTFTGFglkAwyTRwz9ofV8inZbtJBNJHEKdwYS3rGN0ONMjPJNjZOx/Qky7PGx6IJ2za2Zyn2frZXE08U7W978Nx7VMZb2Urs1MzZ5R9UO3wPadPcFe1tXLLYWuneS6V/loD+xUhOcKb0ZL7jPlkUPapT/AKsdMz5MBxO6ODc6DyWi2Lj629RjGcA/Egfes3GNVtujWDfu2+RnD2N+OfuVPMeq2bnRYuVyZtNsH/y0NHBsYHzXNdpXZp5B3vaFvNq5t65VH6OG+4Lne0knZiH2pCfcP2rAxluxHZZcvTw5P8ECi0iPi4p15w12O5NUwxAzvxlPRs6yaKMfXe1vvK7Fvths8nivUuS+WdAP8n2frDw6ulcP9nC5XKNF1C/SdVsvcHfbaGe9wC5jLwXN43Lb/J3/AFl9jhD4RXzqFKptQoMnFaMTlbmMuTR5pxybcpEUZMQiRokrIwiggUEjASjCJGEAKCNEEaXYBhKCSEaUdEeYn2KOxPsUMi5VIlxLc7Cyb9tucB+qWSD4j7gsJGVrNgpt26VEJ4TU7h7Rg/iqOQtwZ0nR7OzIiVm1zN26tfykiafdkfgqYFabbSI7lNLj1XOjPhnUfJZfK1MGfdTFmH16n0c6xfL2aOxyDr4T9phafd+xaimeWuB7tVi7LJumN32JNf39618R1wsnqcdWbOx/TFysxe34NFttF19ukeNd+ASD+iQfkSuZSD4rrD8VVhonO10MLvaC1cpnYY3OY71mEtI8QpumT2tFT9QU+JD1HXmFgiljbNCDkNccbp8Cp4qW1T2x0TGQzHg5+c+Q5KhclwTmGojkHFrgVux1JaZwspultxXJodm7ZBW1k9LJMWyMbvdkccHB+YK6X0S3d1u2otDp3Edc11qqc/bYewT/AESz3Ll1NU/k3ammqScRSOG/r9V3Zd+K1lXHLR3Ot6olrntZXRH/ADkRw/8A2ST7FM4bi4GZfY5yUz1qEYKrtnriy72OhuEZGKmFshxyJGo9hyFPKxGtPRImLyhlIQygXuFEokMqqvW0VosbN66XGmpjjO49/bPk0an3JUm+EI2vctUlcnvXTPQMkdBYbdU183J7wWN890ZcfgsDf+kHae577Ku6RWuE6GnpfXx3Ybl3vIVqvDtn7aIXavY630tbXUVh2ZraNszH3SridDDTtOXje0LiOQAPtOAF5ouhEcscDf8AF4mQk/pAdr4kj2I5quOKZ0lN1rpySTUzkGTPe1oJDT4kkjlhVrnjAA0A0WpjUegtEM5d3kInVX+wtU2l2stsj3BrDIYyT+kCPmQs4XJymMfpEImz1Re0Px9nOvwU0+VoSK0eqrwBU21hPNmq8y9ItE2O5yHA1JK7Mdjop6AS2bam925uo6qQtqoh4DOHAe1cn25sVfQzONZe7fXHk58M0TvboQs2GttFyLW97OYyAx726cHi0+I1C3sNx6pznxO+hqGidoHLfGfnkLFVjXMJ7NM//R1H3EKfZqh0ttZG/R9M4sxnPYcct9x3gquU3DUonTdEsTsdcvctqmXrJCUgFMb2qcaVh3S73s7upqK0O7+60kcgSuifwR445L7tJM4AyNpIWtJ7jISfkFzkAEa8Fo/4OF+jsHSVJbqpwjjucLqMEnQSh29H78EeZCs4P2yRzf6oUn6cvY7H/Ccq5abow6uAkMq6+CGUjmwbz8HzLQvO9ht1I+1RSTwsldMN5znDh4DuXrfpF2YZtrsdX2UythllDZaeZw0jlYcsJ8OR8CV5Jq7btLsrVPtdxs9TFOxx3Wvhe8HxY5ujmnkQrFkZzh21vT2Y3ScnHx7nLIjtNGq/g+zSWrpnpKSB7upqWVFM8Z4s3C8Z8i0L0/0jU8dV0d7TQzAFj7bOTnkQwkfEBcZ/g79Hd1ob3LtZtHTSUknVvjo4Jm7sji/1pC3i0Y0AOpyTwwuh9O+0EVj6Mbu17w2ouLPQIG83F/rH2M3j7lJLmSRn2yi5ylFaT3o8fMDXWJ1QWjrRUMaHc8FpJHwXsroFOeiDZgf93d/vHrx/JBubLCQ8JKsOHkAQvYHQI3HRBsz/AKu7/ePTrZ9y/wBybIq9LsWtcJnDen+OOTpqMcrA6N8FGHA8CC06LIVdNT0e3NphpImxRmppTut4ZMrVrP4QD93pt/8ABo/kVj7lIT0gWY/94pf96ERk/UivbRYhXF9PsnrnuR7qk9ZwHeV5ab/B+2pfO4vuNmjY55dnrJHYyTy3V6kdq53mVwmT+EZaW77Rs7cS5pI1ni5HCZS7FvsMyai/uOt7C7PQ7KbKW+yQSunbTMIdKW4MjyS5zscsknReZume6U9/6XJm0T2yQ0vVUe+3UOdHkv18CSPYpO2XTxfL3TSUNjo2WeKUFhlZIZagg8Q12AG+YBPisjstbX0oNVVtxO4YYw8WA8SfEpl01jwlOb5Zq9IwLM3Iior6U9tmjydUe8m8og5cyz1tcLRJYdMrL7RSB9cWA56mHX9Z5/4W/FaIytYwZOM8ysNXtuc3WVzIaMU1XIZIjJVNDywdkdjiNBzWj0irvu7n7HMfqnK9LF9P3kQZI8ngupdEFE1tUJi05B49y5dDDXyOAzb2uJ5yOPyC6fsRsfca6Nrp9qmUUWhMdDTF7/Y5+gPsXVyfHJ5fNfJrenOuYLNDTNcC58kYA78ZcfkFxArZ9J1tobPV0dNR1Vxq5iHmWetqOsc/hyGjfYsUSrVC1Az7HuQRKTlGUlxwpRqCPFSYqodW2OpZ1kYGBr2m+R+5RETimP8AI9EiWjpJtYpAD9lwwU1BaI55erL42507egTJ1OSjEj2+q4hQSrTLMLpR42Saqz1trbuzxvnox6s0XbdH4EDiFFdSGqj34gJmj6zNfhxCdbW1DBhspATvVxi3vqpGjrnOwxw0Oe/T2qlb0+Nj3Hg2sXrsqYqNq2iq9BZvYe1jj+m1WdHE+nb1kPU0oH841oa72O4+5R3V9SRjrThMOe57svcXE8ycqvHp0t/VLgvT6/TFbqr5Lmgmjihq5Ymu+jafpXcXH7h8SqJpI4q2mHo9ijbwfO7Ps/cBV1FH11ZDEdcuGfLmtKNUakoRRzl2XZkzdtrLO8nqqaigHFrN4/v71WNznClXmbrbjJrkMAaP39qZp27zgEtj3IMePCHY2nC6R0WUmXdcRxe53uGPvKz9VspWUmztPeHgeizkhhz3LbbEReh2CWZwxuQZJ8Tl34LG6m+2GjtOgKM25R9imvs4kq6h/EOe4jyysHtE/emjYNSGk+84WruEnHyWOuDusuThyBa33alZvT4d1yN7r1qpwmhxo3QAptmj6y8UbeW/vHyAJUIq52Si626yScooj73HHyBXR5c+ymTPPej1O7Nrh+S622l6nZmOPOstQB7ACVziV/FbbpJm3IrZTZ4NfKfaQB8isFI7isTEWoHV9an3ZD/AxMVDkOqkSlRnaq/E5m1jT005OO1TblIinJiUSNEgYEgggkYolBGEEAGEpIalZQAfNKCQltSiocYn2qO0p5hTJIs1vklRFXWzNR6NfKKQ8DJuO8nafeqKMqVG4tw5pw4ajzVWxbWjaw7OycZfBtdsabettUOcTg8ew/hlYHOQuoXQsrqVkjdWVMIOfNuvzXMC0sJY4Yc07p9id0yf0yh8Fn9W0athevEkTrW4b74+9uQtlSydZFG/PrNBWGonBlVHk4BOD7Vr7Y8+j7pxlji37/vR1OvcVIX9KZHbOVT9za2V/X2Krh+tEesHz+4rBbSQ9VdqjAw2QiVvk4Z+eVstkpg24OicdJoy32j9yqDbGmLBDJjWNzoHezUfes/Bn2WaOj6xT6lDfwZNybOvFOSJs8V0tb4PNMqGpMtqr+UWinmPrRnccfDh+C1Tb1FNb7RWPdvVFO7EzBrluN149rfmspZiJoKqlJ9cZb5/vhIt9d6K/dlBMZOoHEFXG/EjKjWptwbPSvQhtNBDBNsxWTNbUQSF9GXOwJY3a4HjrvDvDvBdbzr4rxpTPjrIYcueOr0hqIDlzBnO6RpkA8NQRyPJXzr9tIylNPNtXWinAxjek3sfD+8qVmMpy7ovWxzqtgtNHpa+bSWaxsJutypqY/Yc/Lz/AERr8Fz289M9CJDBs/bam4T8i8bjf6oy734XC5au3RSOe7ra2Y8Xyv0J8QDr7XFFcLhM+2xvpn9XTuO66NoDWg+TcD3qavBh/NyVpzkvwbm+7f7UXYPbVXSG1wHjDSHDwO47uT73BYuSsomPc/dkq5TqXzu0J/Vadfa4rPvnc71nE92eSS6VXYVwgvpRG1vyXVRdppIzG1/Vxf5OMBjfc3A9+VWvmJ0ycBRRLkkEhOQQyVMrYoRvPPw8U7a9hdCjKmy7Kl3C2mihDnzse/eALG8QlUFsfVQGZ8rIYuALuf7EjbYaIOUCcjAKk3KgkoSxznCSJ/qvbpr3FRWpop3/AKPbka+xM33dosafbjB+IK5/0rR4fkd5TvRjd/Rw6FxwGv3fY7UfEFK6TMT4LeCqyjqTJa/KOJVQ7RQtdR6JcGb5AimG4/7j78KZcKYxuOQq2aPeYRzVS6HcmmauPc6pqcfY1Dmlp3TxGiYlqooHsY89p3cQMeBJPFN2mr9Moxv/APSIcNkB4kcnfcVGuMD3Shwa5zSOIGQDpkfBZEaE59smdpfnz/bq2hbZbxv3mndyNSC0jBBHEEclVXmhlbIK6lLmyRkOcWHDgRwcD3hS7U2RscjpQRvOG6CdQAANfcrFhwoVL0LNxLrqXUMVRvWm/wDB2vou6b7ZcaGGh2vqGUFzYA30x4xDUfpEj1HHnnQngRwXZqO8UlTA2Skr6eWHiHRTtc33g4Xh6ttEE7i+ImB5+yMg+xVh2cqA7DJICPMj7leV1M+d6OUu6Jl1S1GPcvwe19qukTZfZimdJdbtTun1LaaneJpnn9Vp08yQF5U6QtsLl0lbUMmlZ6NQwAspqYO3hTxk6uceb3YGT5AaBUFFs65pHXzNDSdRG3X3rSUcENLCIqdgY3ie8nvJ5qO3LrqX8Pll7p36euumpZC7Yr/JW7SNbT2KGKNuGRysA8sFenegO/Wo9FNipnXKibPTRPjlifO1ro3dY44IJyNCCvOtZTx1dK+CYZY8Y8R4rPHZeQvyyeEjkXsOVDi5EHDssemXOudIvtuVlEdrWje9OVdR3XpkdLbamGqiYyliMkLw5u+0doZGhxkLJ3iRlNtna6iZ25DHLTyPceTWyAk+wAp6zWVlFM2eaQSyN0YGt3Wt8VMvVsjubGEu6uaP1X4zoeRCe8uuN0deEtBT0LJ/0+cJLUm96PYdTtXYaejkrJbzbBShpk630qMgt8MHVeJtnKamuFZVGpi6yMAubqRjLj9yYGyk2/nrqYc8hhyFo7Lbo7bTljHF73nee8jGe72Jb8qFdbVcttlfpHQr/wBzGeTDUV8k2moaSl1pqeOM/aaNffxUnOEgFArElKU3uT2egwhXUu2taQ5TySVLqllIyOV1MwPm3544g3PAZeRl3gNUijqm1cW+wFupBa4YLTzB8Vl5LVXflOoYKWqnjnkc6KWCPfzvcj3K/t1M+3U8kdTuiUvJcA4EA92eHmrWRj1QpjKD3JmLhZ+VdlWQtjqC8EfaWqdFRGJjsSznq2+A+sfYPmslJKDJhowwANaO4Dgpl2rRV1D5gSWkbkPg3m72n4AKrHFb/S8T0Ktvyzh/1H1FZeU1F/THhFnbtZ2Ad67lscPR6AOzjDc6+S4fZW71WzPeuvRVgp7Jub2C8Yz3Dn8Mq/JbaRzs3wYDbqt9M2glcderaG+06n5hUITtbMamrnnOR1jy4Z7idPhhM5VxLSKL5YCURU+2UsdTFUGUOJYMtwccimbdE2arijlGWE5IxyCNgMejTuj6xsTyzGd7GmEwxr5XhkbS5x4ABX9xZXTyPEG6yIDdDQQC5VtvqW0cc2Y3da7QHu8PemMdFkWWmngAM0TmA8yNEySr6GR8tlnfVHe44JHHu+KoXHv4ofA6L2JwXHDdSdAFLu7xGIaZh7Mbcnz/AH+aFsYDP1r/AFIgXEqDUSGaZ8h+sc+SR8IcluQ2lRsMkjWN9ZxDR7Uk+CsLHGDWdc/83CC4n5femJbeh8npDl/kAnigZ6sLAMeP/thJsTAJZah3qwsPvP7AoE8pnnklP13E+StHD0WwAH16k59n/sPil3uTY1rtio/JUPcXyOeeLjlPQHBCZHFPwhVpM08eG2kX9NW1lVT09uNRI6ndIA2Mu7IJPILpkjhS7LSbunXv3R5cPkFzXZeLrbgHYz1Td4eZ0HzXRNqn+j0lFRNOOrZvOHsx+K5/qdvdJRPQeiYyhUnryzG3B+pysfE/rKhzz9Yk+8rQ3qbcp5nZ1xgeZ0WegG63HdorHSa9ycjP/VmRqEal7kklanYiHMM8x1MswYPJo/ElZMvDWlx5DK6FsdS9TQ0bJBg7u+7zOp+as9Ws7ae35Mv9J0d+W7X4ijH9I1R1m0ckectgjZF5HGT81knnirK9VJrrnV1ROeulc/2Z0+GFXOCqUx7YpE+fZ32yl+SLIVHepcjdFFkCtxMSwYdzTZTjk2eKl9iqwiklKKSU0aBBBEUAAIFJCNABjilBJRoAUjBRIJQQtqdYUyOKcYU1k8HySoypURUOMqTEVXmjTokb6wyGp2bh1y6nc6I+XEfArHbQQdRdZQPVfh49vH4rRbDT7z6yicdJWCRo8W8fgfgoO19OdyGYD1CWH28FUxZelk69mdP1Sv8AedJU15gZrOOa1NpqN8td/lGZ9o4/espk5VrZp91vPMT97+ieK18iHfW4nH9JyP2+TGRtrZUGmrIZh9R4J8uautr6ProqlrBrLH10f67ePw+azULgcY8x5LXtl9IsVLUjtSUzg13iOB+5c0penNM9PnFXVtfJyqTXUJgq0vdJ6Hcp4GjsNdlni06j4FVjhqumontJnmfUaHCbQ7Qzej1TJM4AOvlzUm6xdXVucPVk7Y+9V6tCfS7U13GSDQ+X/t8loV8powLV2y2HZZC7rqYuLesG80g4wUw6V+8WyFxc04OTlRoZHQSslZ6zTnHep91jHWMqI/zcozkd6evtInKSet8MbEuVZ2qVsrJqST1ZRlvgR+/wVKxOxSOjla9hw5pyFJGemRThwOSAxvcxw7TTgo6eOSpmbFEMuOcZOOClXRomjjrI9GvGHDuP76Kuie9jg5jnNd3g4KJPTEjyjSSUM77LDTtazrmuydR3nmj2chdBPV9buiRmGZ7uf4KBJXn8iwtZUO9KDu1hx3sZPP3J/Z+pzPPHNId+YDBceJGmPchCNPQ9NbKeopZZ6SqfNKzJfvD1jxKrfSqmppoqFjWuYSA0Aak+atqKJ1ppap9S9vaGGgc9CB7TlO7P0AZRiqaA+eRp3c8GjgneRvgj3zdgoaWj3t6RmC49wxhUqsbpQVVO11RUyRvL3YOCcklQaanlqqhkNOwvkecABAu9LbJ2z1Waa5sBOGSjqz4a5B96112n9Ojja8drIBWaZYjGcSXKgY4HUGQ5B9yvmw/QsnE0M4YWiV0TsjKbOGtNhVJW7UPJldraFrKlzWjGAsbMzdJB5Lp20VN1tc531SMhYG605ZKSBoVXvh7os41m12sqIpZKKrbUwgHGjm8nDmCtRE6KoiZPAQ6N40PMd4Pis4W66jRCjqZbbMXxgvp3/nI8/EeKysijuW0dH0zP/by7ZeGacJbSmaaWOpgE9O4OiPMcWnuI5FOtWZKDR2FWQpraY81OtTLU80qGUC/C0daltTbdU41RuJZjYOAJYSWpxqY4kqsDBTjSkhKak7R/qDgTjfNNtTgSdgOwUAlAIgic9rGlzjgBHaJ3iy8xtO64tBGDg4yFmL9cOsL6WN26wD6Vw5D7PmfgE7d7ue1BTH6THadyjHj4+Czc0gI3WaNBzrzPeVqdPwHOXqT8HK9f65GmDx6H9T8sD5DJJk6DgAOSXGzLgE1G3JU2laTK0AZXSpex54n3y2y0tMPVSsee9aK83Ittz25ILh1TfbxPu+aiSta2niYxv0rlW3MPlkDWHeZEMaHnzKk9PT2JdNaIGUWS05HLVBEnFQvrfXyzw1DyxoMbc4GddCoVLXPqrlTvmDGkAtGNOKr2uewENc5oPEA4yk65zkgg5GNEgui6p2TC/Skh/VkHyxjRRxR+mXWoA0hbId4j5Jk3as6rc6wfrbo3veo1NWz0od1LgN7V2Wgo8AkybeJZXkQwwyMp4+GGnB/YqR54qwku1Y9paZG4IweyExboRLNvv/NxDJz8AmPl6Hr6VyOzn0W3si4SS9p3kq7Q8FsbVBT/AJHqrvNStq5Q4hsbtQ1oIH35JVbeZ7VV0MM9NHFT1ocN6FgOC3ODyx4olEbGfOjP4Vo8eh2YNziSpOT5f+3zWu2jslNLRROpaeKF8crTIY2gEsOhyp9ot9JU2cyT00Mrnh5YXtBIaMgY9yVQ0mI7k9HMYYuunjiGm+7HkOan32dr6psLPUhaG+398BaTZagpqPZ2e9T0wqp27wa067oGBp4nOSe5VW0FZabjboqqmjiprkX4fDGDq3XU6YPI54qNrtgSxn32eDPDipUAUdnFTqWN0j2MYO08ho8yqVktI6DBpc5JG46P6Dfkhe4D6STrOH1W/tU7aer6+51DgctadxvkNPnlWez0bbfbampA7MMYij8cftwspWyEk5OSea5a6fqWNnpmLUqopfCM7fZc7jBzJeR5KvjG6wDuTtwf1tY/B0adwezj8U2eC6Xp9Xp0pv3POf1Dk+vlNLwhUUXXzwwDOZZGs9nP4ZXRaqpFFYLhVM0c2EtZjvPZHzWM2ag624mUjswtwP1nfsyr7befqLJS0gPank33fqt/aR7lndRn6t8a17HQ9Bq/adOnkS8y8GA3MNA7hhJMeVI3dVKpKV08oYwZJVymrfBgZN3GypfDlQ5o10d+xdWaIz9U7dxnOFirpSup5Sx4wQrjo7UY37mNj+llDIzimHDCmyt4qJINVC1oN7GkRRoimMUCJyNJcmgEjRIwlACUElKQAocEEQRoAUltKbbxS2oZJFkiMqTGVEYU+wqGaL9Mi6sVZ6DdaWo+qx43vFp0PwK1m0tEJoqiEY7Yy0+PEfFYON3Bb+in9PsdNMTvSRjqn9+W/sws3JTg1YvY7Los1dXPGl/MjmuvtUq2ydVVN3jhj+w72/tT9+pfRblIAMMk7bfbx+Kr8aYW9VNWRUl7nA5VMsa+Vb8pm4oXkxAH1mHdPsWt2UmbI+oopfUnYSPPn8PksJa6jrGRyH+dbggfbbx9419q0FvqXU1TDMzjG4O8xz+C5/Np7LGj0no+X+5xov3G9raI9RHMR9JTu9Hkx3a7p+YWSe3VdZ2gpIp5A7P8nro9wkcA7i13yXMZ4HxTPikGJGOLXDxC0OnW90dMxOv4yUvUXhkAsU20ydVVbrh2JBuHPwQZTl/JXdn2Tu93Zv2621VQwfXjjO77+C3q1rk4HKlGO0yiq6UwVL2cgcg+CsLfGKuhkpHeu3tMJ/f98rYT7A7SVMETnWarEzdHAga/FIpej7aiGZsjbJVZac4w32jip49iflGdK9OPk5/uFpIIwQcEI90rot06O9oZJhNDaKo7/rDA0PvUT/k62m/7Fq/cPxQ+z5BZEWuTKWx4O9TTepLoPApiamdDK5j+IPHvW0b0c7T5BFmq/wDZ/FWM/R/tHUUzXOs1SJmaEYb2h707ug1y0MdyT4OcCNKDNFuv+Tnab/saq9zfxQ/5Otp/+xar/Z/FJ3Q+UK70YZzXO1cScd5ylN3uAcfYVtv+Tvab/sWq9zfxSh0dbTHGbNUDz3fxS90Pkb6yMZBTy1EzI4WukkccNbnmr6XqrPb3Q0cgkrZSWTTN+rgZLW+8arVM2E2hoYXQ0NqndK8YknaW8Pst10Hiq6r2B2mjpwXWapLWZOGbrjr4A5T1KuPutkErVY+fBhyTzVjs9cxb64ifWjmHVzDjgcnDy/FM1tDNSyuiqIZIpG8WvaWkeYKhOGOKZOPctF2i705KcTdVlE6SIwh289g3mOB0ezkQsVdaQvD43Ah7Sr7Zu7hzI6GqeGFp/k8xPqn7B8Cp1zoY6ipc9w6uVww5vLzCiT7l2SLVtfa/Wr+1/wCDls0e44gphw71fXikDJXDnnVU72KpZDtZZhLuWyLE+ejmMtI/dJ9Zn1XeBCu7fdoKrDJB1M/2TwPkVUlvgE3LCyQdpuveqdtCn4NLE6hPHevKNe092qca7VZGCpq6XDY5OsZ9l+uPI8VPp760ECoY5h5k6j3hZ9lE4+x0+N1Wm7S3pmkYU60qsprjTygFjwfI5UyOaN3B4VdxNau5NbTJjSltKjtcO8e9LD+8j3hMcSdWkhp1TgKi9axvF7fekmthZxf7k3tJPV+SeClZ71QVO0FNFloeHO7m9o+4KsqLzU1BxE3q2nnJqf6o+9PhROf2oqX9Tx6F9czVVVwhpo3Oe9oA4knQLO192mqsiJzooseuRgn9UcvMqqe8ueHzOdJIOBcc48hwCZkkc/iVpY+BGL7rOTmeofqKy1OFH0r59xckg3Q2MbrPn5ptpJOEGjJKmU1OXkboyStiuPsjlLJdz22FC0nDWjLlqbFbA2Pr59ANdUi0WcNPXVBw3xVrW1LWUwcW7tM3QNGhkPcFPxDliVxdnEPHuyDX1HVfSDAkeMRjub3qnMjs6aeSFTO6eZ0jzq7kOAHcE3zT037lS1qUuPA+GicdnAlHL7Xl4prdOcYwUbBrpxV1a7fPeKmGmpYXy1shw1rR6/n3eaelvlkE59hUNizpzRmncOS65RbG2G0R/wDPMktyr2+vBTv3IYz3F/Fx8lLfBs0W7smzNK1nDLJ5A735TVJPwtlaWXFM4lJGQmHhdau+w9Dc4ny7LyyiqaC42+pILnD/ADb+Z8CuY1lM6J72SMc1zSQQ4YII4jCXSl4LFV8Z+CuLS47rQSToAOanVRFJSNpmnL3dp5Cco4mwROqpRoNGA8z3qvne6SRz3nLnHJUbXaiwn3M0FkmulotTrhAIZaF7u0xxzrnGcDUKRtDTUtdYqa7w0wpp3vaHNGm9kke3hoVT2faCstLHxQdXJA45McrcjPPCkVF3rb7NFHOIo6eI9ZuRghoPLPehNPgbKMk9m4rOrNc6icS2SrpngE8Bud39Yn2Jq1zNFwrqGM/R0dFHEMd5DifuWKu20lXU3eCtaIWyUwLY91pwQeORnVHZr3V0s1yrnCJxqPzm83iddBr44R3rehqpetlpbZ7rY7JHXUwp5KHRssbzk75OOHEeaLaWnpLjs9DeaelbSzOeA9rRgOBJB89dQVR2TaOvtQlbCY5IpXbz45W5aT3ju/YnLzf6y8MZHUdXHAw5bFE3Az3nvUM7Fot00T7kVMY4LQbLU/WV3WkdiEZHi46D71SxszquibF2pzJYI3t9X6aTPfyHyWLm3dkGd10PE7pqUvC5Lq/OFDZ6ShHruG+8fv4n4LEXGfqonvOu6MgK82irRV3GaQOywdhnkP3KyF6mOGsHfvEfJY+NU7JpHT52SsbHlNlWwnJyc8s/NKyAMk6BIAwMJyKI1E8NO3jK8N8hzPuXW8Vw/CPKtSybte8ma3ZKkcyijc4duZ3WH28Phj3qp22rRPfHxNOWU7BCMd/E/E/BbCleyioamrc0BlPGXAeQ0HyC5ZUSvkmkkkOXvcXOPeTquaok7bpWM9D6mli4teLH2Q8H5V/spLEy5QmbG5kZyss16eiqXRkFpwQt2iens4jLh3xcT1WbzaG7Olu9Hnc4ady807aTRS3SUw43c8kxJfasxdX1zy3uyqSqndK4lxySrc5x1wYONiOmTk2Q5TqVEm4qTI5Q5Dqqki/EbKJGUShY8JJKUUlAARhEgEAGjQQKAFBGkjgnIhlwHFKgCASxoVvdm+ji6X2xS3Kka3qY88TguxxwsTW07qaZ8b/WadVLOmUVtkdV8JycYvwIaU8wqM0p5hVWSNGqWiZG5avYqq+mqKJx7Mzd9o/SH7PkshGVY2+ofS1UNRF68Tg4ez98KpdDui0b3Tcl03RmXe1dGX0vWgduE5P6p/cLJLp10ZHURNmj7UE7M+whc3rKc0tTJCfqHA8RyKf0y3cXU/KJf1bhpWRy4eJeSdY5Xb8lPnV30jP1hy9oytTTSdYxrhwcMrCxPdHI2Rh3XtIIPitdb52va0t9WQb7R3H6zfYrOdT3w7l7FH9O53o2umXhm9srvynY5aJx+mhO9H5cR94WY2iousdDXMbjrPo5R3PHA+0fJTLFWmir4piTuZw8d7T+HFaS626M1D4XYFNWDId9l/f79fasrDn6NvPhnX9QpWTQ4+/sV3Rps1TXa5TVNyGbdQR9fO37fc32/d4rTX3aytqH9VTyOpKRnZjgh7DWju0TuwdO+k2J2qZI3dlY+NjgsdXZMrsnTK6yrT5PHsypyukpexPF/rmPJFbUYP8AnHfikSbRXFjsenVWOX0rvxVxB0dXqejhqJH0NM2Voc1s8+67BGRnTj4JR6N7u5mDWWjTh/Kx+Cf61fyUJVQRTxbSXB2WmuqtefWu0+KB2guLTg19Vp/nXfirhvRpdz/jlo/82PwTz+ja6uA/llpDv9bH4JfXq+UN9GPsihG0dwH+PVP9q78UbdpriDpXVOn+dd+Kf2j2JutitwragU81KXBpkp5N8NJ4Z04HvWUwQnxlGS2g9CJqH7R3DAIrqktP+dd+KbG0dwP+PVH9q78VnmuLW4JAB70A06Jy18CejE0TdoK8nHplST/pXfilu2irWDBrKgn/AErvxWdGWsyCE05x807hDHRHZoztHW/9bn/tD+Kcg2juDXhza2oDu8SlZbtHgUthLTqkB0ROoM6rbq1S265CM3aOMvo6rGHEgZ3Hd4K4jWxujkc1wLXNJBB5eC6j0dyuG1Ftwf53HwKwm2TA3aW7Nb6oq5QP65TIrUml4ChtS7TOg41yr+33kSRNp64kkDDJSdR4FZ92hKQTqmTipGtj3ype1yvguLlRl2XBwIWfnp3NPDVdVtdBaqrondXyxn8p0r5G7wdgubvaAjnouY/lKkqXFoeWP+y4a+zvVZ8+WXJWRnzBaKyRhBTDiE5cZMu3YnYIVW50rMF+qgnNReiWupy59ieCORCXutcNRlQ4pmO4nBT+9p2XKH1l7ln9o2txYbqSInOMHvCU2KVg+iqZW/0iibMR6xSxKDzCf2wnzoi9S6rhNoNslc3hVO9rQUsS1x/xr/YCIPR9YE30K/gd++yPHexWah3r1MvswPuSTC1/5xz5P13EpJmA5pt9T4pyqhH2EeRfZw5MltbGxuGgNHcNEHP0wD7lC6/ePHRDrmjih2KPCFhjSny2Pk5RAZ0HFRH1JPqDKVE6TeBKWNgk6NeCfFG4kaK/tX0I3izJ5KupDGxrTKdTy5rS7GSUNz2jpaKpY4U7j2iDuk+HgrMbXApypUvuFPqSGdbWP3Yx6sTeLlUV9XJVy70hw1owxo4NCnbYCFm01wZSsEdOyTdjY06NGBoqYlWIx39T8kN2RuPpVrUQwUtuqbBTjFIioyTA3JXXthqJtn2RNyaAK+4udHG/nHC04OO7Jzr4BcmpG9oea7bGwM2e2WiA0NGw47y52SnzXCRQyZ8aIV6uMGy1NTt6mGpvlQzrWsnBMdOw8CRzce4rMt6RNoRL9PPTTR8DBJTM3CO7AA+aY6SZnVG293LjncmEbfANaAAs7KN9kbnDtagnvToVKUe6XlkcIRSOp0VRS3i1tvFsj9EkieGVNO12RE86tcw/ZPwKp+kq0R1sFDfWNDDVZhq90YzK3639JvHyTXRrK7F8p8ksfQOeR4teCD8Srnart9Gs/HsV8ZHtaQVE/pkvw/8ADGLUJ6Rxu5S9bJhv5tujQquTRWNS3BTdsbA660raxm/TOkDZG5I0OnEeeUtq5Nat6RWkE6Aaqwkf6HRdQ0/TSauPcP30WhrNnoaTa6OnYzFLI5nVtznQ+tr4YKl0totVbtbcKV1OTBT07dOsd6+defcQFEouI52pmFYwyPa1o1JT9xeGMZTx+q31vErWbNUVpZs5UXO5QSPMUrmHccc7uQAAM95SbrabK+0097t7akUnXtbUQucSXN3sOxngfbzSOOkPjYnIxDdAnotSt3S27ZeostXdYrfVinpnEOa6U7x4cNccwm9nLXZLxLeH01HM2Cnp2mJskh3g7ddk6HvA9yrTg9Gjj2pvlFPs5Qirrmb4zFH23+OOA9pXTSBbNn5ak6VFT2W94zz92SmOi6wUk9lqXV0bnTlrZNHEEEgkDT99Vaugp7xe54agb1DQxBmGvLQXnxHdgrnsuMrrFBHoODdXjUvft5Ob1T93OTgBZipl66Yu9v4BazbSlbbbrU0oH0W+Nzv3Dgj54VTthb6a23SOKjYWRui3yC4uyd4jn5LQ6diOO5swv1J1SNnbRB+eSlz3q22YgL6yWodwjHVsPidT+Cp3uIHZGXE4aO89y3Oz1u6iOCnH1NXnvJ4lO6pf2Vdi8sj/AEtg+tk+vL7YDe2tX6LZaeiacPqXdY8dzW/ifkueyFXG1Fx/KN4mla76Jp6uP9Vug9+pVLjfeGjmeaz8avtiafU8j17Wxpz8JJk8VNv1tdaqhkUkkb3OYHgsOdD96py9aEdxZzdz5JDpPFMvkTLnpD3ZU/cUJRDkflR3HJSicpBTG9iJaCKCCCaKJciRniiSABBBBABhGkhKwlAMJcbt14KQEaFwB0XZrpKulhsU1spXM6mQEAkZLc8cLDV1QamodI45c45yogKNTStclpkddEK5OUfLFjinGHVMjinWlQNFuEifDTzOhMrY3GMcXAaJ2Iq0odqZ6bZmWzCCAxyOJ6wjtDPFU8Z1yFXkjXrlBJdrNxstVCrtctE49uA78efsnj7j81T7UUnZbUsHaYdx+O7kf371Ds9a6gr4ahuoae0O9p4j3LXXemY9rvrQzNyD3ghZ7k8e5WLwdbRGPVMCWPP7l4Ocq3sU57VN9cnrIv1hxHtHxCrqqB1NUSQv1c06HvCKFzo5GvYSHNIII5ELo4tWR/DPOJKeNbzw4s3tFI17A4cCNFvrA4XWzmjef5RBjqyePh+HuXN7XOyWNkjNGy5O79l31h9/tWpsNY6hrI525IGjmjm08Vh34zhPR6Hg50cmhTXk6Xa2tOxe0EuMSOEQkHi3TPu09i5pXDtvI8V1i1hh2evMrMOilDHEDgdFzS7Uhp6iRg1jILmHvC28SzcNM4XquL/HsnFcbOhbXX6ClvcdrvUAqrLUUcLnsx24XEHttPf+/nhtqtl5LM+Kqp3sq7VUdqmq2AFrh9l2ODvn8Fd9KjMbRQf6jD8ip2z5fs3s4520p6y2XEgR2xzcveCdZRr2MDXx04HClhLsipL+xzrr0c4cGnBDQO8YWt2d2fo6e3C+7T/Q2tp+ggxiSrdyAH2fn5aqzms+y1kcbxLc2XWjd2qOhYR1j3d0ngPEDx7jVbdR19zjp7+aptbbJWhjDE0tbSu5xlv1deZ4+5Suz1OFwiGUdF3Pf57/ALBbUSyxxw08ElPHT08Yw2Jm8NPPxWC2ctT71fqK3xu3XVMoYXfZbxJ9gytJYR/8M9q/9NT/ADCjdFOG7fWouxq94H9m5LH6Iz7fb/8AgReUb2/XbZrYqtgs8NhiqGhjXzyFrS4A95cCXO540Vbtha7TsrtDab9Bbo6i11G+JKQAbhcWZBAOgBBzjvCo+mFhG21aTzgiI/qLSdLuGbB7Osf64dHp/wCDqoYx12Pf3eRW/u/BorHcbBddlK29x7O0ccdL1mYXQxlztwA8cY5rJWu6WfajbewR0thpqOGPrutjLGFsuWaZAGDjHNSNhD/8Hr8f9Z/uNWW6JDnbu1/0/wC4Uka0lN/AspN9q+TeXy9bM23aY2Os2apSwuYx1Q2GPdBeBjs4zjVc+6VdnaXZzaCNlvaWUlVH1rIyc9WQcOAPdwI810jah+xFHtZLW3qon/KkRY90WHuZkNG7oBg8ua5X0j7TN2nv4qII3R0sLOqha/1iM5Lj4k/cnY+3JOKevcSa1tMe6Oz/AIUW3/Sj5FYvbM/4TXY/97l/vlbLo7P+FFt/0o+RWM2y/wDmW7f63N/fKvL7/wDYr1r6zNycSm05IdSmiUyXkvR8F1bbm+O01lCHYbIN4A8D3rDVlO5sh8T3K/jkMUgkZo5uuVO27s1RYoaN0opnPqadlTuxS5cwPGQHNOCD5ZVa/Wi3j63rZi3CTdwSdOCac+ZmrgSO9Ebg5p7TB8k4yvjPrRuCotqXkvxc4faxh0sbwDggpImdnAdonpn08x0jcHd4CsbZZmSgOndus+2Dw9iaodz0iSVkorufBVh7z3p+EPPAFaWOwUTh2a6MeDwWqfBYm7m7HNTvHhI38VPGiaZBLIrkuWZQb3iiJd4rY/xbld9XPtCQdmJvsEe0Kb0mVvVRipXPHIqM5786renZvHrvjb+s8D71Gm2dowcyV0DPAOB+SjlTJ+CeF0EuWYkyPHMoNkz65PktTPYqRzXiCfrXtaSPq72OQzzWbqIGwSATNI8NVDOtx8k0LVPmLAypPCNmvvUuCOZzg6QkAHRMR1kEejGfBOflF7sBjGt7slCUVyK5zlx4LWNrgzIBJ5niSrXZeR9NXOqvVEbSQVW29txkpy+OjlfH9aTqyG48zotRtHapLNHbo3GJ0dVSsqmOjcTneyCCcDgQrMNTK1jVa3sq6md1RUSSv9Z7i4hNZTYR5VxGa+RYOqej4hR2qRBxCdEazb9H+zP8YayoM8/o1BRxiWomxkgcAGjvP3LqclZZBDb6dgr+roYmxRu7OXBpzk+KyfRJ/wDLO1Z59XD83IpJPpCMp2u+T2/Bl3blLRf3G2bKXS5VNdUtuomqJDI8Me0DJ7kzJs/seGAFt304fSM/BJsdvmuNQyKEZce86DzVnFT2SsqjQUN8pJrhq1sQyA53c13AlMajB67mR7l7Eazx7M2eWofSsuZM8LoHb72HDTjh46KXVv2eudlks8klfTwzStk67su3HDQZHcsxcon0tQ+OQFrmnBB4hM0ry55Ce6Ytb2xm5Lkwu2Nin2fvdTb6lzXujILJG8JGEZa4eazbWsMoEp3W54rqPTez/CmmdjjQQ/8AqXLZzglNjJygpM16Jd0TqkUUddU2y7vI6mKleXa5GdPu3lldg5zU366VL870sReSfF+VT0+0tTT2GS1NjYY3hzRKSd5oJyQOXf71Gst9fZpJZKeBkj5Y9x2+4jGudMJspokhTLTRorDNSR7DVsldC6WkbM4vYw4LtW/fhL2xe2l2atlPbImMtk7usyCSScbwB88k58Fk4L1NDYai1CGMxzOLjLk7w1B4cOSksvssmzjbPNTxPjY7ejlLjvN1yBjhzI9qglbHRcpxJuSf5NHYW56N77/pDr7GKz6JKNz2XlxHY3GDz9bRZmz3OobZqiy09PHIKx/rkkFpIH4Lf7GRSUFTGyjIMUTfpcjSTPH3n5LOycuNaR1HTujzuUpNF3si51JZrrPwIZvA9xDT+xVtjpJ5dkakU72MqawkhzzyzjPwKjbVbVSzw1FBSQxQQHsvew5Lu8DuGeayO0W0slTbKWgjhbBHCPquySAMZPx9pVPHlGc1rk18+q2uqU5cJ/8A0W3SlTOfUWysOC5wEMpbqC4HI+/3LP8ASHpeYAcZ6jH+0VFO0Uj7HFbJKdj2RSCRkpcd4YdkD4kKZWbYMmeJJrPSzP4N3zvHOeA0W9HtjHR59b6t13d5KOw0/pFy6zGYoNfN54LW3iqFrsEr2nE9R9FH4ZGp9yj2ikJlLRE2N8jzI9reAJOSPIcPYs/tjcm1lzMUTs09MOqYRwJ+sffp7Fy+RZ+5v2vCPT8WpdM6eoP7peTPylR3OwcjiE5KdVFeVbgjnL5+4dRK6U9txcfFRHcU446ppx1ViJlWPbGyUlx1RlIUiKzASklGUSQQCIo0lyQQJBBBIKgBBBBAMCUElGClEDKMapKMIAUjScpSADCW0pAShogkix5hUiN2FFaU6xyiki3VMnxPW02ZqxXWx9DIczU43o882d3sPzWFjcrK11j6GtiqItXMOSO8cwfNVL6++Ojoel5rx7VL29yx2joS+MTsHbj0d4t/Ys81dErWRzxsqIBvwTNyPI8QsPcqQ0dSWDPVnVh8O5TdMyNr0peUN/VPTVGSzKlxLyS7FVCKYwvcGslxhx+q7kfu9q2lBLvkB2jgcEdxXOWla6wV3XxguI6yPDZO8jgHfcfYtW6r1Fv3Rz3S8541nZJ8M7rsE4z7KXaGQ7zWua0eRHBUtxod5kkDhl4y6Nx/fn81ZdHLus2W2hDT2w2N2ndqnKrFZBvD88z9/iq32PaNGE1kTshI0e0NojbcI7/LRzXIx00LKWjhYXb8gGd5/LdGR++Fza+2/ae83CWtr7ZcJJ5P8y4Bo5NaOQCtKq83enpB6FcKuJsQw6Nj9AO8D5qhm2v2i+reK3+0/YrNKflHOZWJZRJojO2Zvp1NnuGT/mHK42Yg2gslTIH2OvqbfUDcqqV8Di2Vv4jkVVDbLaTP/wCs139f9iUNsdoj/wDeK3+v+xWe2bWuDOnGT8m4vNihsWwG0L6ZzxR1skEsMcrS2SPtAFjgdchczs9VU0N0p6qiJE8EgkZ5jv8ABSLjebxehHT1tbU1TQctZI/IB7/2p9jYbTR5eBJUPGg7/wAArGPQ+19/uUrrPT0l5Og3LafYy/vp63aGmqIbhA0B0bWuIcAc7uRo5uc8ccViekjbIbU10DaaN0NBTAiJj8bzieLjjhwAA5LJTySSvc55y48VGLXZzjRRxx4QltexMm5L6jpGy21tqtvRzdrPVSTCuqOu6trYi5p3mgDJ5cFnOj+9U1k2soa6ve5tNDv75Y3eIy0gae1Zo73IJDs80KlJS/I7zo1/SJeqa97T1dwt7nupZGxhrnt3To0A6LLB287VNRSOYe8dymMhEp34+PNqlhHtior2Gy45Zqujj/5otv8ApPuKxO2Z/wAJbt/rcv8AfK6D0cUzjtNb9DkPz8CudbZSNftJdnMILXVcpHiN8pPE3/Qhq5mzPSnVNE4Snu1KbJ1UbZopDkcZmlZGOL3BvvOFddNkvW7XPjB7NPBFAPDdaArbYnZCqr423yucKOy0jhM+aQayYPqsHPJGM8OPFFteLRf7rU1cMLo3SHe+kcXEn2aDyWdlZddfDZt9N6PkZb7oLg5C4drB+Sm0FFDM8B8YIPsV1c9mnRt6yn3gDw3vVPhnvUa1xPjyHtIe0kOB4gqvRdC77SXOwL8J6sX+5DoKKE7QQQFshgL+00PPDnqtLVBjaiRkeeqa4hoJ4DOip7UAb66R5DWtadTprwCsp2yxTvZOx8cgOrHggj2FaGNpGTlb4BnCI4PHCTnKBKtFPQeg4fJDjxCLKGUCoPQch7keUnKGUgCt7CavcNPLsvNOYnGqZUNAkEhGGYORu8NTjVGXJ+pp3u2bqTI17I5ngRPeN1ryByJ4+xRXJOJNRtS4MVBAwnLsnzK0FilFLVxviDWOzxAGVTRgN/BW1no5qydu52WA6u+4LPco1R7pGpVTZkWenWttnSq2olrLM8Svkk0+scqPte81OzOyk54tp5IHf0Xg/etNsZspPdaTBf8ARgbpLnYz7lcbQbDQ1dDS2emqPRZ4nvkpy/L43ucBlpJ1bnGnEJlPUKnJItZXQsiteU38HE8olLu9BUWuvmo62Pq6iJ2HDOR7DzHioRPctZSTW0c7KDi9S8i2nVSYDqFDaVKgPaClgRyXB2PojGdltqz+hD83Jl7C6Y496mdEkL49lNqDKN0OZDjPHiVDrJQX7rBho+KdX90v6/8A0Zk+ZcGp2bjdVWu6UNLIGVVTSvhieTjDiNBnx4Lmtkslxqtoo7bDC+KtglBkDtOoDHDecTywt9sS7evFIzOhkbnyzkqj2JkrXdJbqmalqmw1s1QxznQuA3X72MkjwCRy7HLXuiKO+UWW2lSypvVVLD+bc8kHHHllVtsAe/HNLvw3ap4PEEgpi2O3ZQQpVxHSBLcNhdN7f8JKY/8AcYf/AFLk1RqSvQnSNFbrxcWWupd1dYykjlifjUAg6jvGmoXBb5QVFsrZKarZuyN4EcHDvHgoIL+Ei3h3KU3X7lRIcJCXINUloOVVm9G9TDYA3KfibjijijyVo9nrT17zVTtzTxnstP8AOO7vJUb7O1bOi6fhStkoonbN0LqSJs72k1U4xG3GrGn7yttX1DbLZxTxkelzjLnDl3n7go9lpxAyW6VugaOwPv8AuCzt3rZKupkmk4uOg7hyAWBbN3T37Hd10wpgoLwiBVzDdcSdAMkrMV0pfOQePPw7grK5VO6CBxzprxP7PwVKfHJPeVtdPo7Y98jif1F1H1J+hW+F5AHY4q02fpfSazr3D6OA4b4v/YFU4fI9sUIzLId1vn3+xbqwUDIY4oI/UYNSdMniSUvUsn0q+yPljP0z039xf6819MR271YtNlkmZpVT/RxeGeJ9g+5c2kcBwV9tVdBcbiTE7NNENyIeHM+0/cs5I7is3Hr7Y8mv1XK9azjwht7slaHYnZaXaq6Cjp5oonEZzIcBZp5wU5SXCeik36eR0bu9pwVeijn52JPkf2mtjrNdqihfI17oXFrnNOQVTOKkVlQ+plMkji5xOpPFRXKWCKF0k5NoSTlEUEScyDyBEgUEjBg5JCU5JSCAQQQQOQEEEEAwIIkaBoaCARhKAYRjgkhGCgBSUElAcUCpjrSnGlMA6pxpTWTweiVGVJjcoTCpEblDJF+mw2Gyla17XW+cjdfl0RJ4O5t9qcvNCJ4HRkYkacsJ5FZWGRzHtcwlrgQQRxB71uKWqbdqATjHXs7MjfHv8is62LqmrYHZ9Ouhm48sO344MGMh2HDDgcEFTbdUvpahk0eN5vI8HDmPapd8oSHGpjHhIB8CqtpXR4uQroKSPPOpYE8K51SO3dHW00VrqhM8GW31LOqmj4ndPH+kD++q6Kyzek/yixzw1tK4ZG7IA4DuIPMLzNYrn6FNuSEiCQ6/onk78fBbmkr3M+sWu57p4+0ck6+KX1D8CMrp/RLUv+TrdXslcHS9bDTYefWG8NVQVvR7dXS71NSdh2u7vjs/FU9jvTg/0eeeTqX6Al57J9/BTa99RQSlj5ppKaTQZkdqOY48QqcMpVy7TbyOkX5EPuWwz0d3sH/oR/rt/FJPR/eRxo8ecjfxWavUlZSPY6GpqJIJdI3CR2c9x10Kgvu0tBAXSVEz5naY612vx4LVpm7FvaORzOnZFL7WdAi2LulLCeqot+Q898a/Hgqyp2Hv8she+ic5x5l7fxXNZ73WSSukfVzlx/zjh96Ydeqz/rc/9o78VP3y1pNGTLCsjLb8nSm7A3skA0JH9Nv4qbHsDed3c/J5LD+m3PzXKBtBWCn6plTO3JJLutdkju4pLL3Wj/HKn+1d+KE5ezRG6LX5Z1Gbo6vTT2aFzh+s38Vmr3s9XWqQMrqZ8JdqN7gfas1DtBWsd2qqd7e4yu+Gq3OyW1kE1KbZey6qtUh0e470lM77Q5keHu7kv1fhiNWV8sy0dL2sYWws+xd2qoYZ4qQ9VIA5ry4AEHhzT152cktszHsc2aklG9FOzVr2ngmOk6qmpLfs4yGaWNr6HtBryM6juSb3rt9xkrHN6RpJa227E0srp62CW+yxmOKOM7wgzpvOXE7zRTRudKD10bjnrBqT4lQ6iocc9pNQ3CanOI3dg/VOoQu2O+7yyxVRKHKIbznPcpFlpBcLxQ0bjusnmax57m57R92U+99JWnX6CY+4qTYrfVtvMfo0TpXMY92Y+Q3HZPgBlQWrUW0aWNqU4xkdO6R7v1GylnttOGwirb6a6NmgZGdImeQYAuaxnJVx0gVxrL5CGE9XFR08bfACNqpICSuQy03M9a6SoVUpI3nR7HSV8lVbLk0Op6phaN76r+RHisHtfa32x0czCcPlkppOWHswfblpHuVzbJ5IJWyRkhw4FVe3da99tY17jl9V1p89wglGHY42xTIOuYysxrJb48lFabHM+4zFrxPNEzrAeG6A3ecde7K0d6r6eo2boaKcTSXGkDpPSJDkbhcAYmnmG5Hkc4Wc2ZrJGNkex5aXFzHa8WniFKqXVE8tRG0OfHTRSPcAM9WHPAJPcM4WrRJu+T2c1m1Qj0+tJb35ZEBwjyUlFlbhxuheUMpOUMo2GhWURSSUWUCaLGwik/K0ElyifPSRHrJIWetNggNjH6ziB71b7SUY2j2rloqZz6eOpma2GKocQICdAwjlunI9iz1E2dzpjSsc+WOPrsNGcbjg/PwRU9dJHVmo3/pGybwcO/jn4rJ6i2ltex036fjCU3GS8pmdlop4q91E3JqWy9Ruce3vbuPeug09FDbLhPRROEjaZ5g3uTnN0cfa7KwLK4/xrjq94ndqmTZ8Q4HPvC2VBK6SR8jiXOe8uJ7yTkrMzZucEkb/AOnaYwyJy+DrfR7eG0pMEjgGk5Gqv9tauMxwyROG80ZyCuT0VQ6PBGQVY1FymmhDJHk4Giy+6SWmdNZhRnb6qY/0wNgr6Kgu0TWtmexjnEDi12QR7Htz/SK5aCuh7QMrbpsvBHSwulbTR4mdyY0zEgnwzosgKSjoda5/Wyj+ab9667psnOlbPLuv1woy3GJFoqSareBCw7oOrzwCuYTR23gRUVQ/qtKqqq5SzN6uPEMXDdZp7yorH4wtKM1HhGDKEp/cdp6J6x9ZZ9qoC4umdDFI1g+yCc4CjTMOc40XONnr9W2K4x11tnMNQzIzjIcDxBHMFbn/AJVKiTWaxWR7+bjE4Z+Kcm020t7KNlEk9x8FpQTTU0rZISWvachwOoWhj2gu72HerKjcxrl5ws5S9IUwi66osFlhi8Y3ZPsym5OlQ6tbYrRujhljvxSy2/MSH0ZS8C7jI6WQkgnXJJ4lJtkb3ztY1pLnEAAcyoc3Se9x/wDl+yf2bvxUeXpRrmMcaG12mjmxgTRwkub4jJwhzlrwPVFjWkiT00VnVbbMFPLiampYGFzDq14BOM9+o96qBX0u1NCKWvwy4Rgljxpnxb94WOr66asqZZ6iV0s0ri973HJcTxJTEUrmSNexxa5pyCDqCmRtVcVF8o06cHu0/cVcqGWhqnQztw4cCODh3hMxx5WoZUsvlIIKnAqWeqQOPiPvCg01nqHV/ou6N4al31Q37So5Mox+pPg6XAxZz0muQ7Da3VtTuklkLNZH9w8PErpdhtHpr2RMj6ukhGMY4Du8yqyy0LT1VHRj6MauceZ5uK7LsPZqGpppKcyBrWDXB1JPNYV03fLtj4OzjGPTae+Xk5RtXUte8U9PpTw6ADgTw+Cw1xl3A7gCBz4DxXStv7ZFbbhNDA7fYDpjmuS3ubeldGCCAe0R8vIKzj4XPPgq9S6vGmjUPLKmok6x+dd0aN8k1kYJ4BB51KftlL6dVhrvzMesn6Xc39+S05zjVDb8I4nHoszLlCPLbLLZ6gJ/lcgIdIMRgjg3v9vyVztJW/ku0imjdiqqh2iD6rOfv4e9T6YRUlNJV1PZhiGT49wCwN3rZK+tlqZsb7zoOTRyA8lzm5ZNrsl4PQ7+zpmIserz7kKRyiyFOvyo0mVfjE5W6zY28plxS3FNOKmSM2yWxLimzxSnFIUiK0mA8ESMpJSDQIIIiUgCSggghggIIIIHgQRAoBAgaCCCBGBGiRhKIBKSUAgBQRogjQAoFLBTaUCgemPsKeY7VRWnCfjBPAZTGizXLRKY5W9kuLrfViUAuicN2Vn2m/j3KlblvFPsPBV7IbWma2JkSrkpx8o31bDG5gliIkhkGQeRBWOuVIaOowNYnHsH7lc7M3JrP5DVO+gkP0bjwY4/cfmp9zog8PhlB14Hn5hVMa6WJbp+GdL1DEr61iepD70Y8EhaPZ6474ZSTuAeNIXk6H9A/d7ln6iF1PM6N/LgeRHeEhrsFdJGSsj+Gecasxbfho6PFNjzHHPJaqzXSOtpvyfXEkkYjeTqe4Z7+7vXObPcjWMEb8GsaMd3WtH/AKvmrSKTeDXD39yxMyh1v8HoHSc+vMr/AP2RpKsSUUzqepzJC/lycO8eKx20FDPT1HXFxkp5Pzcnh9nwK31qq4b5R+h1jsVLRlj8anxHj3hV1TTvo3SUtZC2WJ4wW8nDvCr0Zkqn2yL2ZgV5cfH1I5vKVGc45Wgv9ofRHroSZaNxw1/Np+y7uPzVE5i3KcjvXBxOb011NpoaLjyRwvb1rOtc5sedSBlTLdb566dsNPGXyOOA1oySl3uzVVqlMVZC6OUfVcMK4m/JgWRipdj8jdXSviHWwu62A6hw5ef4oqSrfBIHxuLSExQ1stG/sEOYeLHcCpj4qeuaZKIiOXnE7TPkpoy90VJx1xJcHQ9idu4qSI227sM1rlPaZxMR+0z7xz80/wBNEtM5tgNuqGVNKyjIEkZBGN4Yz3aLkjnvhkLJGlrhpg6FTKW7SwN3HYfEeLXITi5b8FV4vbLuiRJZM5TBerSWnpq4F1G/qpOJjPD9/JVVRDLTv3ZmFvceR9qZPa5LkGnwGCuy7CWwWnok2gvM4xPcIZIISeLY8Y089VxyggfWVkFNECZJntjaPEnC770xTxbP7D22y02GBsIbgeAx+KrzlvUSaK1ycVjqxX2+llJzLFE2CQdxYMfEYT9O7GM6LJyelUrpK2hy6F/55g13T4j5FEzaIfXa8HmsjJqafg7Tp3U6+xKctNHQ6aUMblxAx3rP18cu020dDZaI5kllDSfs54k+AaCSqB19qapnVUbHbx03sZwt30P00duuM1bMQ+re3cDuO6Dxx4nvUeNjS7u9oXq3WITp9Cp735HekrZqi2bvcbrSx7aFzWtfE06nAwXA8iVN2VtFzu9dQz2SqoKm2QObLUs3urnJwWkSMI7Q3SRgZGqs+ksiqpWO7tNFjNgLy6w7U084duxucGSDvaVqRrX3a5OXlkW+n6W+Bjau1iz36qpGNIhB34gfsHUD2cPYqjK6d0tW70q7QTU27vOaRknQg6/v5rAOs1fnSIEeDwr0NyjsypSjF6bK/e8EMqb+SK8f4uf6w/FJ/JVd/kD/AFgndsvgTvh8kTKGMqa20Vp/mgPNwT8FjqnvY2QxtDiAe1y5peyQepFe5sLFsheKzYZk1gawXKoqGVL3PkEe6xhyxuTy4uI55HcsHtk2K21PUvqqWouJGHxULSKem8N46vd8B4ruG1tybsx0cMig7E9QwNHhp+C8zVDjLUPe45c4kk96z7oqT2zQxbZwTUWFFT78MskYJmiHWDxA9b3aH2Fa2wVjJYwQRr8DzWaopn008UsRAex2RkZHkfBWn5KqNx9w2eY6op8b09I3LpKfv7PFzO5w8jjnSyaHJbRtdK6j+1sfd4Zt4ZcjOU6yYZOqwUG0nVsIkbI144g8lKoq66Xqf0Sz08r5ZNN4DJA7/BZrx5yetHWvrONXX3d+zrXRpcKea8SU0mHU1RI63uJPZcerLj8SAuc7XWmSw7RVtvkziJ/YJ5sOrT7loKOJmzDrNRQyh81LKZ6iRpyHSuIyAeeAAM+avenijZLJarzCP+kR9W8jmeI+9dBjx9KKiedZ17ybpWv3OUlyAdokND5HhjGuc48AArKG3shaJbhIGN5Mack+H/srSTZSbSGaSGapeGwMLjzPIe1WzHUtsbmQieq+zyb+HzUCqupMXU0bBBENMj1j+CrS9x8XKTvUPHkZ2OfnhFlV3GWpeXSuz4DQBHRMlqnjd0jHFx4BMw0gij62uduM+xzJ7v2JFZcHzDq4m9XCNN0c/NHe1zIcq98RRJrnwsl3YHl7QNSe/wAFEMmVHBPenGDKhlbvks10C8+5OxpAarC026a4TbkQw0dp73aNYO8qnbeo+Tbw8FzaSRJs9JPV1bI6UESDtb2cBgH1ieQW3Eb5NympsyOJAc8DBkPf4DwUa307IY2UlAxxY4jecR2pXePh3BalrqewUXWz4fVvGGtHy8u8rDysyU32x8HdYOBDEipSX1CZJY7Bb8NLX1kvz/AfFV9s2oq7dvuZM7tZJOVnq+tkqZ5JpXb0jtT4eCpa+v6mPOd4n1G/a8fJS4MJOWkM6pk141TlZyy82j2hkqXl7nuMzsgHPAHn5rE1Eu8U1LVPkLnOcSTxJUaSU5GAXE6ADUk+C6LaitHm19s8mzufuOtjkqJ2QQtzK84GeAHefALZ2W2tiYyGLJaNSTxcTxJUKwWz0VmXjNTJjfI+qPshTNo7iLXR+jQO/lkze0R/Nt/Ernc3Jd8/Th4R3fR+nw6bQ8i77mVW1t2bUTiipnZpoDqRwe/v8gs2e0cJDnalPUAD52tONVZx6UtRRidQzJWN2SEOp3kZDThQp2luhXqXZjo9sE+xsdTO0Pnki3y7PqnC847WU8dLdKiGIgsY8gFaDpWuDmqupK+bjozkiaJ0S3u1TLiodaJpSCJRIIkgwBRIIIECKSjJRIACCCCQckBAoIikFCRhEEaUQNBEEaAAhnVBFzQJoUgiRpRAwlBISggBSNHCwySNYC0E83HA96SlFXA4ziFqdnbW2sA3jhZNp1CtrZdJKYbocQpau1S3Iba5OP0FreaFtI9zWnOOaqGu1TlbXOndlxJ9qiNcosjtcvpLeJOSiu5k5jlsLJcBcacUtQ7+VRjsH7bR94WIY5SoJXRva9ji17TkEcQVnXUqa5Ok6bnyxrFJePc011oevjLHDdkbq1378ll3tdFIWSAte04IPIraW+tju1KcgNq2DttH1h9ofvoqu724VDS5vZmbwPf4FGFmOiXpWeC91vpMM+v93jeShZIWuDmkhwOQQdQtXabiKxmuPSmjL2j+cH2h494WQO81xa8Frm6EHiCnIZXxSNfE9zHtOQQcEFbk4xtjp+DhsfItw7e6PDR0SnlLXskjcQQchzTghbO2VlPfaYUldhtWPUeNN4948e8c1zS0XNta3GA2pAy6MHG/4t8e8K5imPZcxx46EHGCudy8WVb5PROndSrzYbT1IurlRS0Mz4pmB8bxjdOrJB+/uWTvFj6pjqihDpIBq+M6ui8+8eK6DarxT3WnFHdd0Snstl7+7yPjzUO5Wuptc2+zJjJ7L28PIqvRkSplpl2/Hhkx7Z+THbFXj8gXmGu6sSGM53Xc1K6RtqRtPcRUiAQta0NDRqdE9cbNFWb0tEGw1PEw8GvPe08j4LHVkb4nuZI1zXtOC1wwQV0NOZGcTiOodCVd3qtcldJxKaa4sILCWuB0IOCE9I3JTLmkclZU9mNbQ4+xYx10dQ0R17c8hIBqEiooXsb1lO4SxHh3qvKXBUy07sxOI7xyPsUymn9xRlU19oQcQQQSCO46hTIrlIG7k7WzM8eP7UZnp6v8+3qpPtjgm5aCVnaj+lZjOWp3K+1jHp/cjZ9FVupLjtxbpIgQ2ncZnsPLA0+Ks+n27Crv/o7XZbCwDRO9BNP1dwudY4fm2tZk+0lYPpErzWbQ1khOQXkDyUDe5NskjHWkZZsr4pd+JxY4c2nCdFSXHtxwPP2nRNJ9+FFzkpbE3yTExsr5DhxG79lowPcFrtk6nqJhrjKx0XEK9tMu48HKdrjQGx2oq+tpWjOVzyZ+5UBw0wVpLpUmSIDPJZWqOvmUkVpB5Oh7Q1v5U2SpJd4mWOMAkHm0rEsmlb6ssg8nFW1pmfLaZIXElu6dPYVSjQKaL0irOK3ySBV1I4VEv9coGrqTxqJv65TBQx5p/c/kj7V8DjqiZ3GaU/0yp+zbXS3qAlxIYd45JP78VVq22ay2rklH1Wj5/sSNtjlFF/0zXv0qelomOPVwx8OWVylvIhXm2da6qusr3Ek8FRMzuhU7H9RcqjqJIiHBWtsnlpqmOenkfFKw5a9jiHNPgQqqJToCQU+CBnWbDtAK+JrbvTUVbJ/lKimY5x8zjKuqu5tbSuipWRU0ThgtgjDAfPA1XLrRVmL6xV864F8frHGE1w5E7mQL3IfSA4HUFbq8ujvvRbA+YkupC0kt4gDj8Fzi4S7571vNgZm1mylzoZNRuHTwwpXwkRyRzaS4shZuUMQYPtkan9/FV75HyOLpHlzjzJUuG3TyvLWs3WtcWlztBopJbQ0IO+fSJ+7kD+/epV3Pl+CP6Y8LyRKWilqNcbkfN7uH7U+6enogW0w66bnI7gFEqq2apyHHdZ9lvD9qYGU1zS8D1W5eRc0j5nl8ri5x7+SIBGGpxrFDKZbrp3whLW5UiNhRxx55LT2mw7gbUXRrmRkbzIBo+Qd5+yPiqlt6gts3cHp07mlFEGz2eWt+ke4Q0rD25XDI8mjmVsKSkDmR0lDCWwg6NHrPPe48ynqSlmr5GRwxhrG6NjboyMK9nnpNnqUtbuy1jh++e4fNYWRlStekdtiYVeHFe8hsCnsFKZJsPq38Gg/vp3lZO5V8tXUPmncXPd7gO4JFfWzVU75pnF0jjqcaf+yo6+ubDHvOOc6Ac3fs8UuNjSsekNzs6vEg52Pkcr61kURc7Ucm/bP4LN1Ez55C+Q5J+CTUTvnkL3nPcOQ8E0XYGSdF0lNMaY6R5vn59mbb3S8ewbnYGeXNaCwWxzC2pqW4lIzGw/UHefH5KPYbY6V7aqob2NDEwjiftH7gtW98NvpHVVW7DRwHNx7h4rMzszf8Ks6XoPRlBfushf0CrKyKzUPXSYdM/SKPvP4DmsBV1MlRPJNM8vked5zjzKfu9wluFU+aY6nRrRwa3uCrXuUFFPYtvyS9T6g7pdsftQHvQhnMbwQeCYe9NOer9fBzV8u7g29HtzdKW3GiiqpGw4xugrJ3GqdUSOc85cdVBMh70lz881adrktMzY0Qre4oQ46ps6pTjlIJUTY4BSSjKJNACI8EaQUABBBBIKuQIIIJBwERRoikALKNJCUlACGUEEogEaIIc0AGjCJBA0NBAIIAWCgCkJWUoCkoFICUCl2AtpJ5p1pwmMpTXJrRLB6JTHJ+N6hNcn2OUUkXqrNFnSVElNMyWFxbI05BC2VHURXWnMkQDKhv5yPu8R3hYJjlMoqqWlnZNA/dkbwP3HwVK+nvOi6Z1F470/tZb3e29cC+MBs445+uO4rPHLTh7S1w0IPI9y3dJPDdqYyRAMnaPpI+Y8R4KmuttEx3mjdnAxk8HDuP4p+Hmut+naSda6JDLh+6xPPx8mfjkLHhzXFrgcgg4IK1Fpu4qSGS7rak9+jZvwd81lHtcyQseC14OC08QgCtqUY2R0/BxNN1uJZ3R4aOjwyBwyOWhHMHuK1di2iDIhR3P6WmI3Q4jJaPHvC5babzjdirHkEaNm46dzu8ePFaKOfexyOMjBznxHesHKwXB7Xg7vpvWKsuKhPiRuLxZSxnpNvPXU7hkbpyWjvHeFmLhTQXBoZWxnfGjZ2Dtt8+8KVY77U2126079OTkxuOnmO4rUmhob/C6otz2x1PF8Z094+8KhCU6X+DZlKM49tnK+TkN1ss9B23YlgPqzR6tPge4+BVU+LRdTqqKpt8r2SM3CdHNcMtcPEcCFQV9jpavL6JzaaoPGJ35tx8Dy8itfHzFLhnPZ3SP5q+UYN8Zb5JotV1X0E1JMYqmJ8cn2XDj4jvUF8K1IWJnK34rg/BC3dVJpppYTmN2B3ckDEkFhAIwddFOpa5Rnyr29M7LsW0WnZp1TK4CorYBUOaPqg53R57oB9q4ntBL1lfO4HOXEre369Ghs0kQcXPkkMbATyaA0eQAC5q6arrpjHboHTPz6wZvf8AsoJWqMO6XuTLGk7XCC8DDWuJ0a7HknWtcOR9ydFivsvr9Y3wc/CJ1lvkWoa53kQVT/fwRorpGRrfY/7C2aKwo3lpGOSp3zV1IcV1G4AcXbuP2KdQ1lNOQGP3XfZdoVZryoWeClbizrfKLiaQuYqmqb2gArQNyzPuUGoLRIDxIU7elsihByejWbCWOrvMopKQxCRwO6ZX7oJA4ZUCr2aq6Spkp55adssZ3XNDs4PmtfZBFaLFb7kx+Z3ymPqwcYaGjX3lZna2EOrIKjnLFrp9k4VbDzPVscJLg1OrdF/bY8boS/qQfyFUD+dh95/BD8hVP+Uh95/BVxYeWUNx3itXuj8HLds/ksDYp+csI9pV1aNnayms1dcnPiNMzDcl27vEcm54nVZdrD3ZPitltBchTWGhsccYbHHK5zncyQMD4lx9qp5mQqYbiuTX6R095tvbN8HL7u4TVTnNOWkqK0YGFc7VUTKG5QmKQSR1MLZgRyJ0IPiCFWFucEKnC31NS+S1k4v7eUofAcYUuMKO0NjbvyODGd5KbNwBduUsTpCeZCsO2Na3JlSFUrHpF1A8gaaKUyrdjBKpoaK+VQzHAYx3kBvzUgbN354z1ns31Vl1GtM0a+jZE1tQf9ixdL1nMLWbBVop56qN7iGvjOniudzWm+0X0klPJIwfWaN75Kx2cu7m1sYl0yd0nu81PVlQuWkVcjAspf1Jr+pd7XxT0deIRMXQTQsmYQMAh3EHyII9izhaStPtVI6oZQk67gkjB8N7P3lUTYsngpoTc47ZDbjqqxxRFDCnGxlS2wE8k5HTucQ1gJcTgADOUyUkienGcmRmRqxt1tnrZhHTRF7ufIN8SeSu7ds7u7stzcYmnhCw/SHz7gtDAwmIU1HC2KE6BkY9bz5krOyMxRXB1HT+jSsfdPhFbQWqmtpDmEVNWD+cI7DP1RzPitBarPPcZOsk3hGTl0juJ8u9WttsMNNH6RdHtYxo3tw6DHifuVZfdo3TNNPbh1NONC4aOcPDuCxrJzue2dRUq6I9lK/3Jt0u9NZ4nUVtaHT4w+Q6gfifBY2qqHTPdJK7eedS52ufEpiaUcXO9neqW53MREsb2pe7k3z7yreNhOx/gzc/qtWHF87ZIuVeyBmDlxOrWc3eJ7h81m5pnzyGSVxc4/vhJkkfK8vkcXPcclx4lIJDck6LfqqjVHUTz/MzbcyzumxRIaMnh3q1strNS9lTUs+i4sjP1/E+HhzSrRaDM5s9Yw7mhbEefi7w8FrY2Q0lO6qq3BkbNSSs3Nzdfw6zpeidD8ZGSuFykKiEVLC+pq3BsTBqT8vNYy+XWS5VRectiZpHH9kfieaO+XeW5TY9SnYfo4xy8T3lUznqpRTr6peS/wBS6j3/AMOviKBI5RpHJbtcqPIVejE5q20S5ybLkHFNkqZFCcthkpJKInVEU7ZC2AokeVNudZFVmExU0cAjjEZDPrEfWPik2CSabbICJGiJQNCPFEj4oikYBokEEDktAQQCCRihc0EZSUAEjCJBACkESNCACAQQwlEDQRckaBNARpJRhKIGjyiQQAtBJyjygBYKGUgFHlA9DrCnmuUZpTjXJrRLGWiW1yfY9QmuTzXKKUdlyq0sqOrlpZ2TQPLJG8CFr6Ksgu8OWgRVbRl0ff4jwWEY5Sqed8UjZInlj2nLXNOCFTuoU/6nQdP6lLHevKZobpbG1AIeN2UaNeBqPPwWYnhkp5THM3ddx04Ed4W0tlzhujGw1AbHWEYGNGv8u4+CYudA2RhjlBxyI4jxCTGy50Pss8FzqfSKepQ9fH4l/wD7yZAHCsLbc30gEcg6yDOd0nBb4tPI/BRK6klpH9rLojwePv7k23VbsJRtW1ycFbVdiWdslpo21FWRzsD2PL2czjBB7nDkrmiqpaaZstPI5kjeDgVzqjmkp5Q+F5Y4d3P8VpaC6MeAHgRPPFv1D5fZ+Sp34ClzA3sHrzWoXf3OpW/aSkuMLaa8sYx506zGGnxP2T8E1dtnHtzLRESxnXdzk48O9YeJ5dnl3gq8st5rbdhsbw+DiYnat9nd7FmSw5Qf0nQV50ZLcXwNyBxZ6PVxNnhGQY5Bq3yPEFVdVs1DOC+2z9rnBMQHew8Cuhx1dpvUbRLiCoxgB5Ad7DzVRcdn6qN2aRj6hp4brTkKamdkXrRBkPHuX18HM6u2zU0hjnifG8fVcMKI+l46LqsVhvVTGI6iiL4e6ocBjy1yEVT0eSOgklbNDTOAzuFxkHkMBatdkmvqRzGVTVCX0TTMnsrsVVbeXqCNxey2wAune043ieLQeXifxXZTsDYrPRtgjIY1o9WIBo/fzV/bqOj2A2PhieQyXcy883PXO63bB1RUPkcN8E6NJ0Wfk2R9zb6bjWSffWv9yBtHZKGl3n0kxI+y78VmepaeAWqjqKe6zONU9kTeTGDCkx7LNq5QKR5Oe7VYlke57gdlTkKmOrjIChimYQ9zMH6ruCzV92Koqhrn0gEFQdQWeofZy9i6pdtkqm1U/XyODmjiqGCp6jeY9rXsdoQ4ZTYSnXLzoLasbOrf0qSOMCartNY6juLXaaBx+BzzHijqHjrQc5aSNVu9tbNDcqZ/UtAeBvRnmD3eS5jSSuLjTykhzThueWOS6HDyvWg4vyef9V6a+n3xf8r8HTWyF9PBGCcA6eClbU0wZFbo25e8Rvc7A4Zdp8iqXZs1NzMMFPE+SoLg0MA1yvQ9iovyXaoKUkOkaMyOx6zjx/fwTum0Srm5SRP+pup02YsK63yzzmaR2fUf7ik+iu+w/wDqlenxJ5IzJ5e5bfd+Dge5nl90BjG8Wu011BVjtxG1ty6yPVu8XZ8Cc/evRjn5449y490u2Cpiqn3OlidLRzEGTdGerf4juPeqebB2V8I2+h5iov8AqetnItqjl1Gc5IDgPJVUlQIIwXDLj6oT94mMk4c8EMjGBnmVGstG+vrd54JaDqO/uCzIbor58mtlP97luNfhk6zWeou0rZakubCeAA1I8FuLVbaSjaBBCxp+1jJPmVe2OtoLBQB1NE2e4ubgyPALY/Bo+9VrpnzTGV2AXHJxwWZlSlJbbO06RgU4/Hbz8sn07Wb/AGycDuVtTQxSyNa1pGebioVrojVPH0jW+a3Oz+z8TZ2mTFRpwB0CoRg5M2r8iFMeRu2WOglwKiR29+icYVTtr0X09wo5K+xuBrYm7xaRgvA78cfPj5rczWBjSZIo+rP6LlFpqmptNZG8uL4gcEE8lo0TVT01o53K1mxenv8ABwWsikIhjla4Pjb2mniCTkg/BIipi5wABJPIBdp2x2Bp7hfW11DOyCnrIuu3SD2nZ7QBHDiFUs2NuVEMUUFP+s2UF5/rYW6pvsXatnIuut3NWy0Yqi2bkexsla4U0R1w7V58m/irqlpaeibigh3XcDM/V5H3K6p9m7o+bE9NJGM6vfr8lex0dpsbBJXysfPxDXak+TfvKzL7LW9aOhxVi1JOLTM1b7DVVZEjgY4zrvv5+Q5q3nqbds+wsjAlq8cB63tP1QoF82nqarfjo808PePXI8+XsWRnkDcuccZ4qCONOf3F+WckufBY3a6z3GYPneN1vqsbo1vkFSVVS1gcSRgcSToPNQq65Niy0ZLvsg6+3u+aoKupkqD2z2eIaOAWhRga5mYWd19RXZT5JNfdC8ltOXYOhkPE+A7gqolG5CCKWplEdOzfcePcPElaP01r4RyzduVZ8tiCdcDJcdAAMknuV/aLOWubPVAOl4tj4hnie8qVZ7SymIcfpKjgXnl4DuV1VT01pp+uqiHPI7EQPad+A8Vj5Wc7H2VHadJ6FDHj6+V5/wCAz1NBSmprH7rGnQcST3AcysffLvNcp8u7ELD9HEDo3xPeUxdrnPcakyzu0GjGD1WDuH4qte9Q00dvMvJJ1Hqbs/h18RFOfhMPcie9MPcrsYnPW2i3SHVMOcgSm3FSpFCc9gJScoEok4hbAggklAwGUCgiOiBAIuJQKCBQcESGUEgqQEEEECgQQREpAAgiRoASggglEDCNJRhIKGgUEEABBBHhKAOaCCCBGAI0SGUDQ0EEEooaNEEeEBsMJQOEjgjCByY81yda5RgUtrk3RLGeiW12vFPMeobXJ1rlHKOy3XbonMfjmtNar42Rrae5uy3GGz8x+t+KyLHJ1rlWspU1pmxh588eXdFm4raIFnJ8bhoeIIWcq7UWZfTA44mPOvsS7ReJqEiM/S05OTG46DyPIrSM9Hr4DLRO3h9Zp9ZvmFWrnZjS2vBuW14vVq9PiRjYRrqCCO9ToGZ5aK1qLfHK7LwWvxo4ff3pmng9FqIjVRl8AcN7d+s3Oo8NFv42XC9fDOF6n0e/DbaW4/JqNkdmrtdo2SQRtjos6TT5a3x3eZ9mi6Lb9iqGAA1s09S7ub9G34a/Faq3mlrbfDVWp7Jbe5oERj9VoA9XHIjhhKexTvtk+TJhddBaiyvprfQUf/RaKnjP2tzLveclPPldwycJbmFNPbhOUYoilOyX3MQH4KDqyCGqoWVMgax1RGX5+wHAn7k3I4NCxW2m0D7XOyM01LVwSRZMVQ0nDgSN5rgQWnyRNd0WkOx2o2py8Culna38s3x8FM7+SwdkY5lYIVJ71Q1+0DJ6l7vye+HJ9WOo3gP6wz8U1HeIebZ2+bQfvXPX9PvlJs9JwevYNNUYeNGtp6l2mHELcbEbQGjrWslf2Hd65LDeKcY7T/bGVb268Upkbmoaw54uY/7gqq6dkRe0i9d1vp90HGUzvu1d1pn2iRocx7njQLj9ZI3fdu6apUt2hMWlyp345CKUn4gLNV9zky7qnNd/Qx8yU+XTr7X4K2J1rBw4tKTZewsbOC17hjvPJZSu2cpqy4VEkFO2aIHedMHhkTe/LzgceWpQjuE5OrWOPfIN8D2HT4J5hqrpM1rTPWSt0Abq1n/pb8Fq4OA8d90mc/17rceoRVdcdJe5f7NOp7RVUjKBwqKjrG4MYLYo9RnGe084zqcDwK7QZRk92dFyrZbZyeKqiqK57Wlh3mxR66+LvuC6LHvY45WvHRxl0W2T+u8UXXeKiEPSHNkTuCDtZNMzccVktvLjHT09MyWIyxSF+9uuw5ug1GdM8dCMHKupGS40Wc2ptUtypOq6wsIO80gZweCR6HQg3JHLLjYqKtmzb6eKre46RsO5MP8Aw3HB/okpi0UEFPHLE5r4a4EgwStLHN/onVSLxablby51TSmaEfzsILgPNvEfFV0l5nlgMRqBVRDQRztEob5b2o9mFRvrVi0b3T75Ytnf5JPXOa4sIII71ZNqA5kbAAN0clkBVyseSWkjkGv0HsOVKiuj2uG9G4jyH3FY1uBY/B2+N+ocfjv2jZ0c5ZwJHkVtNjr/AOg1bRM49WdM8VyynvMOO0Hj+gT96uaC60Lzh9U6M+ML/uVVdPvT2kXbeu9Ptg4ykegJL9QmPe69uCFl7nd4JnuawhwIxlc8FzoMY9PcR3CB6jy3mnjz1cszwO6LHzcrDwcifGjKr6l06jlSb/2Ot0d4gda7dFNK1ssNQ5gBP1HDHuzhW5eMaarhdo2pqaWuMrIKeZzRmN07S4xkcHAZxkLsNulc+30pf6xiZnPHO6Mraxap1Q7ZnJdXuqyru+lcFiJUUzYKlu7UwQzDukYHfNMByUHKw0mZiVkfDKut2VtFWDuwvpnn60Lzj+qchYfaXYW7U7XS2yRtbFza0bsoHlwPsOV04OTkTXyu3Y2ueTyGqalGL2TO6+Ue1y4PMVXCY3ua9rmuaSC1wwQe7CgvIAJOgC6N0tS0VdtOyO1mOeqZCG1b4iC3rMnGSNCQMAlZWktTGvDpQJZBw+yPxUd2VXUtvyXcDpd+Y/pWl8lTSW2Wsw9+YoDzxq7yWmtlubEwRwR7rB7z596mxUjWRGaoc2ONurnO0AVLeNouyYLYTFHwMvBzvLuWFdkWZL0vB3eLg4vSod0uZf5LK6Xans7XRQBs1ZjUfVZ5nv8ABYqsq5qqd01RIZJHcSU1I8knJKjPcpKqVAy87qM73rwvgU96Yc5Bzk05ytqJi2Wgc5NkonOSCVIkUpzDJSMoEpJTvBC2GhyRIigY3sBKCCCBAJBRkokgoEEEECpAQQQRsUCCCBSAESgiRoACSUpJKQABBEjSiAQQQQKKQSUoIACNEUAgQNBBBKAEEEECaAEaJDKAFI84RZQQIK4okQOEfFAqYYRgpKPKB2x1pTjXJgFLa5JofGRJY9OteogcltcmOJZhY0TWPUukqpKeVskLyx7eBH76qsa5Psco5QTL1N7i9pm0oL1BWNEdaGwyf5Rvqu8+5WElOWjOjmEaHOQQsJHIMq0tt1no8NjcHRc438PZ3KpKlx5gb+P1VT+jIW18mlt1dcrHUGosVdNRyH1mNd2H+BB0PtC1du6XKuJwiv1qhmPOSnPVP88atPwWPpa6jrwGtd1Mx+o/n5HmkVdG7d3ZWbzfEKerNlW9WFfM/T9GWvUx3p/jwdgt3SHstXAB9bUUTzyqYTgf0m5Cv6Sutle0GhuVDUg8BHM3Pu4rzPPQuZ2qaTH6LuHvVfNNJC7E8ZYe8jIPtWlXfXb9rOUyul5GK/rjx8nq+ahc4dqI478LI7V7E0d+EbpnVME0YIbJA8A4PIggghcNoNorjREGkuNZAf8ANzuA92cLR0PSVtNTDAur5m908bJPmMqbukikkky0rOiCr1dSXreHIVFN97T9yrJOizaCM/R1FsmHm9n3FXlJ0vXlgAqKS11HfmIsJ9xVvS9MkJwKzZyB3eYakt+YUcpSRYj2vyYj/k42lZp1Fvd+rUEfNqXH0f7SMP8A0WiH/wDdD/hXSqbpa2akwKiyXCM/5uVjvvCs6fpH2InbmVt1gPc6AO+RKjdsl7E8a4v3OXR7DbREYd+To9OPXOd8mqXT9Hdc4j0q4wsHMQwE/FxXVYNrthJxpdp4/wDSUzx9ymRXjYqU9jaKmGfttcPmFG8lr2ZLGiBzai6PbbDg1Anq3f512G/1W4C0dNaI4I2xQwtjjboGsaGgewLaRS7LSj6PaO2698oHzUqKiscv5u/213lOz8U392L6EGZCmot06NKtIqbQdkrTwWW3u9S60TvKVp+9TorFT47NdTH+mPxTo5iILMWDMgKU/ZKBpfBbYWGH/rcH9Yfih+Qof+uU/wDWH4p/7yJD+0j8mFfS6cFCqqQOHBdEfYoMa1tMPNw/FRJ7LRAdu5UTfORv4pHmIkhiwXlnMZ7eHZywHzCobtsTaboS6qoI9/lIzLHj2hddmttmjJ6y+W1vnOwfeoUrNmYvzu0ltGO6Zp+9RvKTLcaa17nDanopp8k0Vwq4RybI1soHyKrJujC7MJ6iuoZR+nG9nyyu9SXHY2L19pKQ/q5PyChzbSbDRcbw+T/RwvP/AKU1X79h3p1/Jwv/AJOb+3h6A/yncPm1OxdH+0LT+aofbUH/AIV2CfbrYeAHdluEpH2acj5kKrqulPZaHPo9ruM3dvOY37ypI2y9kyOcKvk59FsBtA7i+3M/8R7v/SrCDo1usg+nuNNGOfVwOd8yFe1XTBQMJ9E2eB/0tT+AVTU9MVwcSKW122Acshzz8SFKp2P2K8vSRZ2rozpaaZslZUVNWQc7hwxvtDdT71vIaGXda1sbsAY0HBcZq+lfaSXIiqqenH+Zp2g+85WfuO3F+rgW1V4rntP1RMWj3DCkXe/JFKyHsj0XLA2mYXVUsMDRxMsgZ81SXDajZugyKi80znD6kGZT/sjC84vr5amXUyTynm4l5+Km0tDUSkGod1TT9Vup/AJllkKuZyJsfEvynqqJ1a69KVug7Fpt09XJwDqh240/0Rkn4LN3PajaK+Ruirqw0dE7jS0g6sEfpEan2lVFFRNYd2CLBOhdxJ9qmzGmt7A+tlDXcmNGXH2LOtzu7is6fD/T1dX8TJe/+AqSkO4Gwx7jO4DRFW3CjtTSHET1I/m2Hh5nl81R3TaKeoaYqUGngOnZPad5nl7Fn3y+KrKqU3uZoXdRqoj6eOv9ywul2qa+QGd43B6sbRhrfYqx8nckPkTLnq1GCXgwb8mVj7pMW96Zc5Jc5NOcplEoTt2Lc5NOdqgXJsnVPSKk57DJyklFlDOU7wRNgQ5IJJKBm9h5Rc0ESQA0koyUlAAQQQQCWwFBBBA4CCCCQAIuKIoBABoIIigAEouKIo0AEEESNABoIIJAAjCJGUogaGUQRoFDQRIZQAaCCCUQCCCCBNACNEggQNGEQQSgKBR4SEYKQBSMFJQ4IHJjgcnGuTIKUCgemSGuTjXKKHJwOTWiaE9ExsifZIoAcltemOJahaWDZParWgvdTStDHETRc2POfceIWfbJ4pwSeKgnUpeTQozJ1PcHo2kFXQV+A13UynTcfpr4HgUVTQPaDloc08sZBWPD8jVWNBdqukw2KXMf2H9ofsVWdDi9xZvUdVhYu2+I9U2qF2dwOid+jw9yrZqGrg9UCVve06+5aWC80dUA2sidC77TNR+Kk+gR1DC+klZI39E5wnV5l9PnlDbukYObzXw/wYYzuacPBaRyOiUKk8itVU28uBE0Ie3xGVU1Fmgd+bL4j3DUfFX6+p1y+9aMLK/TF9fNT2iuFU7vS21jghJaKlhJiLJG+eCoksM8P52GRo78aK5G+qz7WYtuBk0P64MsWXCQcHYUmO7Sjjg+aoRIO9H1g71L2plbunHhmmjvbhxB96fjvjQdQ4ewFZPfRh6b6aHK6S9zax36IcXD+qpUe0EQGkrPksB1mvFKEnik9KPwO/cz+TobdoWY/Os/rIztCwD86z+sud9ce9H1pzxR6UfgP3E/k379oWY1lZ78qPJf4zwc3+qsR1p70Ot8UvpR+A9eRrZL6zJ3fg1R5L24+qFmOszzQ3/FHpoa7pP3NA+8SHn8VHkucruLsKm3x3ojIB9bCOxITvkyzfWk8/imXVTiocYfL+aje8/otypkVsrJTqwRD9M6+4Jkra4eWT1YeRe/og2INQU2+oxxKtILIzI6+V7/AAb2QrSjtccZAggaD34yfeqlnUqo/bybWP8ApjJs5s+lGegp6qoP0cTg37T+yFZ01lbo6pkdIfst7I/FaWG0uDS+YiNn2nHAHtTM1xtdDoHmpkHKP1f6xVGzPut4hwbVPQsPD+q17f5EUVAWtDYYQxp5AYUuUUlvGayVodx3Bq4+xUNdtFVTgsh3aeM8o+PvVM+Ukkkkk8STxUSonPmbLFvVKqV20RNFW7RSOaY6FnUM4bx1efwVBNO57y57i5x4knJKjOkTbpFahSo+DDyM6y57mxx8iZc9Nuem3OU6iZ07RbnptzkguSS5PSK07A3FILkRckp6RXlLYeUknVBElI2wIZRIIGgJQQRZQAM4RZQKJIAEEEECpAQQQQKBBBBIAEWUDxQQAEEEEgBZRFAoFKAXBEgUEoAQCCJIApGEQKCADQQCCQQCMFDkiKBRSCIFGlACGUEEAGgiQSgGggggRoCMIkEDQ0EQKUEADKPiiQSgKQRA96NAqYoFKBTaMFA5MeDksOUcFLDk3RIpj4clteo4KUCmtE0bCU1+qcD1DDvFLD/FMcSzC7RMbJgp+GodG8OY9zHd7TgquD04H+KjdaZcryWuUzSU20VXHhsxZO3/ADjdfeFPjvNvqNKiGSF3eO0PxWPEiW16ryxos06uq2w43tG0ZT0dV/0Wqjc4/VLsH3FIltdRHwCyPWd+CpdNcaqn/MVErPJ+nuULxmvDL8OrQlxZEtJ7cH/nadjvEtUGSz0xz9G5p/RdhSYtoq1v5wxSj9NmD7wpcd/gk0qKIebH/ikXr1/aybv6ff8Ael/Yo32SM/m5pG+YBTD7JMPVqGHzaQtS25WmQdps8fmzPyS2y2l/CsDfBzSPuUizMmPkhl0jplvjX9zHOs9UOD4j7cfci/JVaODI3eTwtqIaF/qV0GOXbASvQYXerUwn/wARp+9O/wBSvXlDH+m8CXiX+TDm11v+SHseEX5Mrf8AJD+uFvBbByljP9Ifij/JeOMsfvCd/qd3wN/6Xw//ACf9zCC11v8Ak2D+mEptprD/AJJvm5bg26MDtVMLfN7fxSTS0bfXracf02pH1K9+EKv01gx8y/yY5lkqD600bfIEp5ljH85UOP6rQFqs2qP16+I+Dcn5BIdcLNFwdLJ+rGfvwmPNyZeCSPRumVedf3KCOzUwOokf5u/BToLZEw/R0zB/Ryfipkm0FDGMQULneL3AfLKiS7T1XCCGmhHeGlx+KY3kT8slT6bR9qX9iwhtlQ/RrCPABSDbo6cb1ZPFC0facAsxU3m4VAxJWS7v2WndHwUB0hJyXZPeeKFjSl9zGT6xVDiuJr5Llaab1DJUuHJjcD3lQ6jaabBbRwxU7eRxvO950WZMmqS6RTRxooz7usXT4T0vwTauunqnb1TNJKf03ZworpEw56bc9WY1pGVbkyk9tjzpEhz0wXJJcnqJWlcOmRIL00XIi5PUStK0UXJBcklySXJ2iFz2KJSCdUSGUuiNvYESCGUoxsNJJQKCBAIIIiUCAJwklBBIKBBBBAqQEEEPagUCCCCQAIsoZQQASNBEgA0nKNEUAEURKBKCUAIIIJAAggiKEIGjCSglFFIwkgo0gC0RRBGkDYSPKBRJQFIIkYQAAjRI0ABBBBKIBBBBAAQGiCCBBQKNIRgoEFIIkEoCkMIkMoDYeUoFJQQKmLzhGHJGUMo0PTHQ5KBTKMFNaHqQ8HJQcmQ5KBTWiRWaHw5LD1GylBxTe0mjaSd9KD1FDkYek7SZXksSJQeoocjD03tJFkEvrO9H1niou+hvo7B6yCX1nii39VG6xDfSdiHfuGvclbw8EN4dwUYPQ6xHYhf3Mvkk748Pcj38dyi76G+jsQn7h/JK63xSTIFFL0N9L2jXeSDJlJL1H30Rel7SN3D5ekl6ZL0kuS9pG7h4vSS9MlyLeSqJHK0cLkguSCUkuTkiKVgslESkZyiynaIXPYouSSURKLKXQxyDJRIc0ClG9wXJBAlEgQGUEEEABESiJRJADJRYQCCAAggggUCCCCBQIIIJAAUk6o8oIAJGgiSAGkoIIACSUZRJQAggglACCCCa2IBBBBAAQQQSpgBGiQQKGjyiCCQA0EMoJRAI0SCAFDVGEkIwgUNBBBAAQQQSgBBBBAgEEEECNARgokECCkaTwR5SgGgCgggA8oIkEAK5IIgUeUC7DCMFJQQOTF5R7yQhlJocpDgcjymsowUmhe8dBRgpnJR7xSaHeoPbyG+md5HvI7RysHt5DeTO8hvI0L6g+HIFyZ3kW8jQeoP7yIuTO8j3kaD1RwuQymt5DeRoPUHMoZTe8iLkuhjmLyiLkjJRZS6Ecxe8iJSMo8o0N7g8osokEo1sGUECcIsoG7DRZCIlBAAQQQSbACCLKGUCAyiJRIIFAggggXQEEEECgQQQSABBBFlAAygdUEEAAIIIigAFFqUMojogA+STlBBAAQQQQAEEEEmxAIIIJAAggglACCCCAAggglFAhlBBABo8pIRoANBBBAgYQRoIFBlGiQGiADQQQQAEEEECAQCCCUUCCCCBA0ESMIE0BGCiQQAaNJQBSgKQQB1QygA+aGUSCAFBBJRhABoIs6oZSAGEeUWUMpRdh5RZQ0Q0QLsP2oZRIIE2KygkoIDYaCJBAdweUMosoIDuDRIZQygNgQQyiQJsCPKJBAbDyiQyggAiggSiygQNEhlEgA8oiUESQAIZQQQO0BBBBAoEEEEABBBDKAAiJRZKCQAI0ESAAggiSADOqCBREpQDJ0SUEEABBBBDYAQQQSbEAgggkFAiRoigAI0EEoAQQQQGgIIIIEAgggjYoEYKJGlANDgiQSAKBRpKMFKAaCJGkACAKCJKApBFlHlAAQR5RIACCNBKIEjQQQGgkfBBBAAQQ5IIEAhzQQQAYKAKJBKApBJQQAtBJyjygQNBFlGgUCCCCAAhlHhFhAMPKLKGEMIEBlBDCCAAggggUCCGUWUbE8BoIsoFAoaLKJDCADyEWUSCQAIIIIDQESNBAaCQRoIFCQRoIF0EgjRJNgAoIuKCABlBBBAAQQQQASGUESQAkaIokoAKCCCAAggEaGASCNBNECQCNBAoSJKRFKAXFDCNBAH/2Q=="

if __name__ == "__main__":
    asyncio.run(main())
