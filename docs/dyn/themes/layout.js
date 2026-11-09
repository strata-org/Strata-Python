// The layout's "On this page" rail and scroll-spy for both navs.
// Verso pages carry <base href> pointing at the site root, so a bare "#id" would resolve
// against the root page; the rail's links therefore name this page in full.
window.addEventListener('DOMContentLoaded', function () {
  var heads = Array.from(document.querySelectorAll('main h2[id]'));
  if (!heads.length) return;
  var here = location.href.split('#')[0];
  // The same page, whatever its spelling: no query, no hash, no trailing index.html.
  function pageOf(u) { return u.split('#')[0].split('?')[0].replace(/index\.html$/, ''); }
  var otp = document.createElement('nav');
  otp.className = 'otp';
  otp.setAttribute('aria-label', 'On this page');
  otp.innerHTML = '<h3>On this page</h3>';
  heads.forEach(function (h) {
    var t = h.cloneNode(true);
    t.querySelectorAll('.permalink-widget').forEach(function (e) { e.remove(); });
    var a = document.createElement('a');
    a.href = here + '#' + h.id;
    a.dataset.id = h.id;
    a.textContent = t.textContent.replace(/\s+/g, ' ').trim();
    otp.appendChild(a);
  });
  document.body.appendChild(otp);
  // Left-nav entries for this page's sections, matched by their fragment.
  var navLinks = Array.from(document.querySelectorAll('#toc a[href*="#"]')).filter(function (a) {
    return pageOf(a.href) === pageOf(here);
  });
  navLinks.forEach(function (a) { a.dataset.id = a.href.split('#')[1]; });
  var links = Array.from(otp.querySelectorAll('a')).concat(navLinks);
  function spy() {
    var y = window.scrollY + window.innerHeight * 0.25, cur = heads[0].id;
    heads.forEach(function (h) { if (h.getBoundingClientRect().top + window.scrollY <= y) cur = h.id; });
    links.forEach(function (a) { a.classList.toggle('active', a.dataset.id === cur); });
  }
  window.addEventListener('scroll', spy, { passive: true });
  spy();
});
