/* مفاتيح رقيم على الهاتف — المحرّك. (بناء 879)
 *
 * ⛔ لا سرَّ في هذا الملفّ ولا في صفحته: مفتاحُ التوقيع يُستورَد على هاتف
 * البائع ويُحفَظ فيه مشفَّراً بكلمة سرّه، ولا يغادره. وما هنا هو المفتاحُ
 * العامّ وحده — وهو مضمَّنٌ في كلّ نسخةٍ من رقيم أصلاً.
 *
 * ⚖️ صورةٌ حرفيّةٌ لما يفعله الحاسوب، لا تصميمٌ ثانٍ:
 *   - Ed25519 منقولٌ سطراً بسطر من core/_ed25519.py (RFC 8032، مجال عامّ).
 *   - صيغةُ المفتاح من core/license.py: البصمةُ المعياريّة + حمولةٌ (بايت
 *     نوعٍ + أيّامٌ منذ 2000‑01‑01 uint32) ثمّ Base32 بلا حشوٍ في مجموعاتٍ
 *     من ثمانية بعد RQM. ورمزُ إعادة كلمة المرور من core/vendor_reset.py بعد RQR.
 *   - والحارسُ tests/test_phone_signer.py يُشغّل هذا الملفَّ في متصفّحٍ
 *     حقيقيّ ويطابق ناتجَه بناتج بايثون بايتاً ببايت.
 *
 * لا مكتبةَ خارجيّة ولا شبكة: SHA‑512 وPBKDF2 وAES‑GCM من crypto.subtle.
 */
"use strict";
(function (root) {
  // ─── المفتاحُ العامّ — نسخةُ core/license.py::_PUBLIC_KEY_HEX (حارسٌ يطابقهما)
  const PUBLIC_KEY = "3bcb02f74915600bcc35a0f015315f8de014584ca830bff9109d7882c611910c";

  // ─── بايتات ─────────────────────────────────────────────────────────
  const enc = new TextEncoder();

  function concat(...parts) {
    const size = parts.reduce((n, p) => n + p.length, 0);
    const out = new Uint8Array(size);
    let at = 0;
    for (const p of parts) { out.set(p, at); at += p.length; }
    return out;
  }

  function hexToBytes(hex) {
    const clean = String(hex || "").trim();
    if (!/^([0-9a-fA-F]{2})*$/.test(clean)) throw new Error("hex");
    const out = new Uint8Array(clean.length / 2);
    for (let i = 0; i < out.length; i++) out[i] = parseInt(clean.substr(i * 2, 2), 16);
    return out;
  }

  function bytesToHex(bytes) {
    return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
  }

  function leToInt(bytes) {
    let n = 0n;
    for (let i = bytes.length - 1; i >= 0; i--) n = (n << 8n) | BigInt(bytes[i]);
    return n;
  }

  function intToLE(n, size) {
    const out = new Uint8Array(size);
    for (let i = 0; i < size; i++) { out[i] = Number(n & 255n); n >>= 8n; }
    return out;
  }

  function u32be(n) {
    return new Uint8Array([(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
  }

  // ─── Ed25519 — core/_ed25519.py ─────────────────────────────────────
  const P = 2n ** 255n - 19n;
  const Q = 2n ** 252n + 27742317777372353535851937790883648493n;

  function mod(a, m = P) { const r = a % m; return r >= 0n ? r : r + m; }

  function powMod(base, exp, m = P) {
    let result = 1n;
    base = mod(base, m);
    while (exp > 0n) {
      if (exp & 1n) result = (result * base) % m;
      base = (base * base) % m;
      exp >>= 1n;
    }
    return result;
  }

  function inv(x) { return powMod(x, P - 2n); }

  const D = mod(-121665n * inv(121666n));
  const SQRT_M1 = powMod(2n, (P - 1n) / 4n);

  function pointAdd(a, b) {
    const A = mod((a[1] - a[0]) * (b[1] - b[0]));
    const B = mod((a[1] + a[0]) * (b[1] + b[0]));
    const C = mod(2n * a[3] * b[3] * D);
    const DD = mod(2n * a[2] * b[2]);
    const E = B - A, F = DD - C, G = DD + C, H = B + A;
    return [mod(E * F), mod(G * H), mod(F * G), mod(E * H)];
  }

  function pointMul(s, pt) {
    let acc = [0n, 1n, 1n, 0n];
    while (s > 0n) {
      if (s & 1n) acc = pointAdd(acc, pt);
      pt = pointAdd(pt, pt);
      s >>= 1n;
    }
    return acc;
  }

  function pointEqual(a, b) {
    return mod(a[0] * b[2] - b[0] * a[2]) === 0n && mod(a[1] * b[2] - b[1] * a[2]) === 0n;
  }

  function recoverX(y, sign) {
    if (y >= P) return null;
    const x2 = mod((y * y - 1n) * inv(D * y * y + 1n));
    if (x2 === 0n) return sign ? null : 0n;
    let x = powMod(x2, (P + 3n) / 8n);
    if (mod(x * x - x2) !== 0n) x = mod(x * SQRT_M1);
    if (mod(x * x - x2) !== 0n) return null;
    if (Number(x & 1n) !== sign) x = P - x;
    return x;
  }

  const GY = mod(4n * inv(5n));
  const GX = recoverX(GY, 0);
  const BASE = [GX, GY, 1n, mod(GX * GY)];

  function compress(pt) {
    const zinv = inv(pt[2]);
    const x = mod(pt[0] * zinv), y = mod(pt[1] * zinv);
    return intToLE(y | ((x & 1n) << 255n), 32);
  }

  function decompress(bytes) {
    if (bytes.length !== 32) return null;
    let y = leToInt(bytes);
    const sign = Number(y >> 255n);
    y &= (1n << 255n) - 1n;
    const x = recoverX(y, sign);
    return x === null ? null : [x, y, 1n, mod(x * y)];
  }

  async function sha512(...parts) {
    return new Uint8Array(await crypto.subtle.digest("SHA-512", concat(...parts)));
  }

  async function expand(seed) {
    if (seed.length !== 32) throw new Error("seed");
    const h = await sha512(seed);
    let a = leToInt(h.slice(0, 32));
    a &= (1n << 254n) - 8n;
    a |= 1n << 254n;
    return [a, h.slice(32)];
  }

  async function publicFromSeed(seed) {
    const [a] = await expand(seed);
    return compress(pointMul(a, BASE));
  }

  async function sign(seed, msg) {
    const [a, prefix] = await expand(seed);
    const A = compress(pointMul(a, BASE));
    const r = mod(leToInt(await sha512(prefix, msg)), Q);
    const Rs = compress(pointMul(r, BASE));
    const h = mod(leToInt(await sha512(Rs, A, msg)), Q);
    const s = mod(r + h * a, Q);
    return concat(Rs, intToLE(s, 32));
  }

  async function verify(pub, msg, sig) {
    if (pub.length !== 32 || sig.length !== 64) return false;
    const A = decompress(pub);
    if (!A) return false;
    const Rs = sig.slice(0, 32);
    const R = decompress(Rs);
    if (!R) return false;
    const s = leToInt(sig.slice(32));
    if (s >= Q) return false;
    const h = mod(leToInt(await sha512(Rs, pub, msg)), Q);
    return pointEqual(pointMul(s, BASE), pointAdd(R, pointMul(h, A)));
  }

  // ─── Base32 (RFC 4648، بلا حشو) والعرض في مجموعات ───────────────────
  const B32 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";

  function base32(bytes) {
    let bits = 0, value = 0, out = "";
    for (const b of bytes) {
      value = (value << 8) | b;
      bits += 8;
      while (bits >= 5) {
        out += B32[(value >>> (bits - 5)) & 31];
        bits -= 5;
      }
      value &= (1 << bits) - 1;
    }
    if (bits > 0) out += B32[(value << (5 - bits)) & 31];
    return out;
  }

  function unbase32(text) {
    const out = [];
    let bits = 0, value = 0;
    for (const ch of text) {
      const v = B32.indexOf(ch);
      if (v < 0) return null;
      value = (value << 5) | v;
      bits += 5;
      if (bits >= 8) {
        out.push((value >>> (bits - 8)) & 255);
        bits -= 8;
      }
      value &= (1 << bits) - 1;
    }
    return new Uint8Array(out);
  }

  function grouped(prefix, bytes) {
    const body = base32(bytes);
    const groups = [];
    for (let i = 0; i < body.length; i += 8) groups.push(body.slice(i, i + 8));
    return prefix + "-" + groups.join("-");
  }

  /** جسمُ الرمز كما يقرؤه رقيم: بلا فواصل ولا بادئة، و0/1 ⇦ O/I. */
  function ungrouped(prefix, text) {
    const parts = String(text || "").trim().toUpperCase().split(/[\s-]+/).filter(Boolean);
    if (parts.length && parts[0] === prefix) parts.shift();
    return unbase32(parts.join("").replace(/0/g, "O").replace(/1/g, "I"));
  }

  // ─── البصمةُ والتاريخ ───────────────────────────────────────────────
  /** core/license.py::_norm_fp — وهي الرسالةُ الموقَّعة. */
  function normFp(fp) {
    return String(fp || "").replace(/\s+/g, "").toUpperCase().replace(/-/g, "");
  }

  /** بصمةُ رقيم ستّةَ عشرَ حرفاً ستّ‑عشريّاً — وغيرُها خطأُ نسخٍ لا بصمة. */
  function isFingerprint(fp) { return /^[0-9A-F]{16}$/.test(normFp(fp)); }

  /** يلتقط البصمةَ من رسالة الأستاذ كما هي («بصمة جهازي: ABCD-…»). */
  function findFingerprint(text) {
    const hit = String(text || "").toUpperCase().match(/[0-9A-F]{4}(?:[\s-]?[0-9A-F]{4}){3}/);
    if (!hit) return "";
    const raw = normFp(hit[0]);
    return raw.match(/.{4}/g).join("-");
  }

  function isLeap(y) { return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0; }

  /** core/license.py::_add_years — و29 فبراير في سنةٍ بسيطة ⇦ 28. */
  function addYears(ymd, n) {
    let [y, m, d] = ymd;
    y += n;
    if (m === 2 && d === 29 && !isLeap(y)) d = 28;
    return [y, m, d];
  }

  function addDays(ymd, n) {
    const t = new Date(Date.UTC(ymd[0], ymd[1] - 1, ymd[2] + n));
    return [t.getUTCFullYear(), t.getUTCMonth() + 1, t.getUTCDate()];
  }

  /** «اليوم» بتوقيت الهاتف — كما يقرأ الحاسوبُ date.today() بتوقيته. */
  function today() {
    const t = new Date();
    return [t.getFullYear(), t.getMonth() + 1, t.getDate()];
  }

  function parseYmd(text) {
    const m = /^(\d{4})-(\d{2})-(\d{2})$/.exec(String(text || "").trim());
    if (!m) return null;
    const ymd = [Number(m[1]), Number(m[2]), Number(m[3])];
    const back = addDays(ymd, 0);
    return back.join() === ymd.join() ? ymd : null;
  }

  function ymdText(ymd) {
    return `${ymd[0]}-${String(ymd[1]).padStart(2, "0")}-${String(ymd[2]).padStart(2, "0")}`;
  }

  function daysSince2000(ymd) {
    return Math.round((Date.UTC(ymd[0], ymd[1] - 1, ymd[2]) - Date.UTC(2000, 0, 1)) / 86400000);
  }

  function before(a, b) { return daysSince2000(a) < daysSince2000(b); }

  // ─── المفتاحُ ورمزُ الإعادة ─────────────────────────────────────────
  function seedBytes(seedHex) {
    const seed = hexToBytes(seedHex);
    if (seed.length !== 32) throw new Error("seed");
    return seed;
  }

  /** مفتاحُ تفعيلٍ سنويّ — core/license.py::generate_key(TIER_ANNUAL).
   *  ``when``: {years} من اليوم، أو {expiry: "YYYY-MM-DD"}. */
  async function makeLicense(seedHex, fingerprint, when) {
    const expiry = when && when.expiry ? parseYmd(when.expiry)
      : addYears(today(), Math.max(1, Math.floor(Number(when && when.years) || 1)));
    if (!expiry) throw new Error("expiry");
    const payload = concat(new Uint8Array([1]), u32be(daysSince2000(expiry)));
    const msg = concat(enc.encode(normFp(fingerprint)), payload);
    const sig = await sign(seedBytes(seedHex), msg);
    return { key: grouped("RQM", concat(payload, sig)), expiry: ymdText(expiry) };
  }

  /** core/license.py::verify_key ⇦ {tier, expiry} أو null. */
  async function verifyLicense(key, fingerprint, pubHex = PUBLIC_KEY) {
    const raw = ungrouped("RQM", key);
    if (!raw || raw.length < 64) return null;
    const payload = raw.slice(0, raw.length - 64), sig = raw.slice(raw.length - 64);
    let info;
    if (payload.length === 0 || (payload.length === 1 && payload[0] === 0)) {
      info = { tier: "permanent", expiry: null };
    } else if (payload.length === 5 && payload[0] === 1) {
      const days = ((payload[1] << 24) >>> 0) + (payload[2] << 16) + (payload[3] << 8) + payload[4];
      info = { tier: "annual", expiry: ymdText(addDays([2000, 1, 1], days)) };
    } else {
      return null;
    }
    const msg = concat(enc.encode(normFp(fingerprint)), payload);
    return (await verify(hexToBytes(pubHex), msg, sig)) ? info : null;
  }

  /** رمزُ إعادة كلمة المرور — core/vendor_reset.py::generate_reset_token. */
  async function makeReset(seedHex, fingerprint, days = 7, nonceHex = null) {
    const expiry = addDays(today(), Math.max(1, Math.floor(Number(days) || 7)));
    const nonce = nonceHex ? hexToBytes(nonceHex) : crypto.getRandomValues(new Uint8Array(4));
    const payload = concat(new Uint8Array([2]), u32be(daysSince2000(expiry)), nonce);
    const msg = concat(enc.encode(normFp(fingerprint)), payload);
    const sig = await sign(seedBytes(seedHex), msg);
    return { token: grouped("RQR", concat(payload, sig)), expiry: ymdText(expiry) };
  }

  async function verifyReset(token, fingerprint, pubHex = PUBLIC_KEY) {
    const raw = ungrouped("RQR", token);
    if (!raw || raw.length < 64 + 5 || raw[0] !== 2) return false;
    const payload = raw.slice(0, raw.length - 64), sig = raw.slice(raw.length - 64);
    const msg = concat(enc.encode(normFp(fingerprint)), payload);
    return verify(hexToBytes(pubHex), msg, sig);
  }

  // ─── ملفُّ التوقيع وحفظُه مشفَّراً ──────────────────────────────────
  /** يجد مفتاحَ التوقيع في ملفّ JSON **بقيمته لا باسم حقله**: كلُّ قيمةٍ من
   *  64 حرفاً ستّ‑عشريّاً يُشتقّ منها مفتاحٌ عامّ، فإن طابق مفتاحَ رقيم فهي هو.
   *  فملفٌّ خاطئٌ يُرفَض قبل أن يُحفَظ، ولا يُكتَب هنا اسمُ حقلٍ من ملفّ السرّ. */
  async function findSeed(jsonText, pubHex = PUBLIC_KEY) {
    let data;
    try { data = JSON.parse(jsonText); } catch (_e) { return null; }
    const found = [];
    (function walk(v) {
      if (typeof v === "string" && /^[0-9a-fA-F]{64}$/.test(v.trim())) found.push(v.trim().toLowerCase());
      else if (v && typeof v === "object") Object.values(v).forEach(walk);
    })(data);
    for (const hex of found) {
      if (bytesToHex(await publicFromSeed(hexToBytes(hex))) === pubHex) return hex;
    }
    return null;
  }

  const ITERATIONS = 600000;

  function b64(bytes) { return btoa(String.fromCharCode(...bytes)); }
  function unb64(text) { return Uint8Array.from(atob(text), (c) => c.charCodeAt(0)); }

  async function passwordKey(password, salt, iterations) {
    const base = await crypto.subtle.importKey("raw", enc.encode(password), "PBKDF2", false, ["deriveKey"]);
    return crypto.subtle.deriveKey({ name: "PBKDF2", salt, iterations, hash: "SHA-256" },
      base, { name: "AES-GCM", length: 256 }, false, ["encrypt", "decrypt"]);
  }

  /** يقفل المفتاحَ بكلمة السرّ: PBKDF2‑SHA256 ثمّ AES‑GCM‑256. */
  async function seal(seedHex, password, iterations = ITERATIONS) {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const key = await passwordKey(password, salt, iterations);
    const ct = new Uint8Array(await crypto.subtle.encrypt({ name: "AES-GCM", iv }, key, seedBytes(seedHex)));
    return { v: 1, iter: iterations, salt: b64(salt), iv: b64(iv), ct: b64(ct) };
  }

  /** يفتحه — أو يرمي إن كانت كلمةُ السرّ خاطئة (AES‑GCM يكشف ذلك). */
  async function unseal(sealed, password) {
    const key = await passwordKey(password, unb64(sealed.salt), Number(sealed.iter) || ITERATIONS);
    const plain = await crypto.subtle.decrypt({ name: "AES-GCM", iv: unb64(sealed.iv) }, key, unb64(sealed.ct));
    return bytesToHex(new Uint8Array(plain));
  }

  root.RaqeemSigner = Object.freeze({
    PUBLIC_KEY, bytesToHex, hexToBytes,
    publicFromSeed, sign, verify,
    normFp, isFingerprint, findFingerprint, addYears, addDays, today, parseYmd, ymdText, before,
    makeLicense, verifyLicense, makeReset, verifyReset,
    findSeed, seal, unseal,
  });
})(typeof self !== "undefined" ? self : this);
