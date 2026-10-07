/* عاملُ الصفحة الخلفيّ — لتعمل «مفاتيح رقيم» بلا إنترنت. (بناء 879)
 *
 * ⚖️ **الشبكةُ أوّلاً ثمّ المخزن**: متّصلاً يأخذ الهاتفُ آخرَ نسخةٍ ويحفظها،
 * وبلا اتّصالٍ يفتح المحفوظة. فلا تعلق الصفحةُ عند نسخةٍ قديمةٍ بعد تحديث.
 * ⛔ وقائمةُ FILES هي ملفّاتُ المجلّد كلُّها — حارسٌ يطابقهما.
 */
const CACHE = "raqeem-signer";
const FILES = ["./", "index.html", "engine.js", "manifest.webmanifest", "icon-192.png", "icon-512.png"];

self.addEventListener("install", (event) => {
  event.waitUntil(caches.open(CACHE).then((cache) => cache.addAll(FILES)));
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil(self.clients.claim());
});

self.addEventListener("fetch", (event) => {
  if (event.request.method !== "GET") return;
  event.respondWith(
    fetch(event.request)
      .then((response) => {
        const copy = response.clone();
        caches.open(CACHE).then((cache) => cache.put(event.request, copy));
        return response;
      })
      .catch(() => caches.match(event.request, { ignoreSearch: true })),
  );
});
