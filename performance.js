/*
 * Summitbound – performance.js
 * Zusatzdatei: einfach neben index.html in dasselbe GitHub-Verzeichnis legen.
 * Sie sorgt für gleichmäßige Bildrate, fängt Fehler ab und spart Rechenleistung.
 * Das Spiel läuft auch ohne diese Datei, mit ihr aber ruhiger (vor allem auf iPad/Handy).
 */
(function () {
  'use strict';

  /* 1) Speicher-Fallback: Wenn der Browser localStorage blockiert (z. B. privater Modus),
        läuft das Spiel trotzdem – nur ohne dauerhaftes Speichern. */
  try {
    localStorage.setItem('__sb_test', '1');
    localStorage.removeItem('__sb_test');
  } catch (e) {
    try {
      var mem = {};
      var shim = {
        getItem: function (k) { return Object.prototype.hasOwnProperty.call(mem, k) ? mem[k] : null; },
        setItem: function (k, v) { mem[k] = String(v); },
        removeItem: function (k) { delete mem[k]; },
        clear: function () { mem = {}; }
      };
      Object.defineProperty(window, 'localStorage', { value: shim, configurable: true });
    } catch (e2) { /* nichts zu tun */ }
  }

  /* 2) Hauptleinwand ohne Transparenz anlegen (schneller zu zeichnen). */
  try {
    var origGetContext = HTMLCanvasElement.prototype.getContext;
    HTMLCanvasElement.prototype.getContext = function (type, opts) {
      if (type === '2d' && this.id === 'game') {
        opts = Object.assign({}, opts, { alpha: false });
      }
      return origGetContext.call(this, type, opts);
    };
  } catch (e) { /* ignorieren */ }

  /* 3) Gleichmäßige Bildrate + Fehlerschutz.
        - höchstens 60 Bilder pro Sekunde (spart Akku auf 120-Hz-Displays)
        - wird das Gerät zu langsam, wechselt es automatisch auf stabile 30 Bilder pro Sekunde
        - ein einzelner Fehler in einem Bild stoppt das Spiel nicht mehr */
  var nativeRaf = window.requestAnimationFrame.bind(window);
  var target = 1000 / 60;      // Ziel-Abstand zwischen zwei Bildern
  var last = 0;
  var work = 8;                // gleitender Mittelwert der Rechenzeit pro Bild (ms)
  var slowCount = 0, fastCount = 0, errors = 0, banner = null;

  function showBanner(msg) {
    if (banner || !document.body) return;
    banner = document.createElement('div');
    banner.style.cssText = 'position:fixed;left:50%;bottom:16px;transform:translateX(-50%);' +
      'background:#7a1f2b;color:#fff;padding:10px 16px;border-radius:10px;font:14px system-ui;' +
      'z-index:99;box-shadow:0 6px 20px #0008';
    banner.textContent = msg;
    document.body.appendChild(banner);
  }

  window.requestAnimationFrame = function (cb) {
    return nativeRaf(function wrap(t) {
      if (t - last < target - 1.5) { window.requestAnimationFrame(cb); return; }
      last = t;
      var t0 = performance.now();
      try {
        cb(t);
        errors = 0;
      } catch (err) {
        errors++;
        if (window.console) console.error('Summitbound:', err);
        if (errors < 40) window.requestAnimationFrame(cb);
        else showBanner('Es ist ein Fehler aufgetreten – bitte die Seite neu laden.');
        return;
      }
      work = work * 0.92 + (performance.now() - t0) * 0.08;
      if (target < 20 && work > 13) {            // 60 fps nicht zu halten -> 30 fps
        if (++slowCount > 60) { target = 1000 / 30; slowCount = 0; fastCount = 0; }
      } else { slowCount = Math.max(0, slowCount - 1); }
      if (target > 20 && work < 6) {             // wieder genug Luft -> zurück auf 60 fps
        if (++fastCount > 600) { target = 1000 / 60; fastCount = 0; }
      } else { fastCount = Math.max(0, fastCount - 1); }
    });
  };

  /* 4) Weniger Last für den Ton: kürzerer Hall (halbiert die Rechenzeit) und
        Ton pausieren, solange der Tab im Hintergrund ist. */
  try {
    var AC = window.AudioContext || window.webkitAudioContext;
    if (AC) {
      var contexts = [];
      var Wrapped = function () {
        var c = new (Function.prototype.bind.apply(AC, [null].concat([].slice.call(arguments))))();
        contexts.push(c);
        return c;
      };
      Wrapped.prototype = AC.prototype;
      window.AudioContext = Wrapped;
      if (window.webkitAudioContext) window.webkitAudioContext = Wrapped;

      var origConv = AC.prototype.createConvolver;
      if (origConv) {
        AC.prototype.createConvolver = function () {
          var node = origConv.call(this), ctx = this, held = null;
          var desc = Object.getOwnPropertyDescriptor(Object.getPrototypeOf(node), 'buffer');
          if (!desc || !desc.set) return node;
          Object.defineProperty(node, 'buffer', {
            configurable: true,
            get: function () { return held; },
            set: function (b) {
              held = b;
              try {
                var n = Math.floor(ctx.sampleRate * 0.9);
                if (b && b.length > n) {
                  var nb = ctx.createBuffer(b.numberOfChannels, n, ctx.sampleRate);
                  for (var ch = 0; ch < b.numberOfChannels; ch++) {
                    var src = b.getChannelData(ch), dst = nb.getChannelData(ch);
                    for (var i = 0; i < n; i++) dst[i] = src[i] * (1 - 0.15 * i / n);
                  }
                  desc.set.call(node, nb);
                } else { desc.set.call(node, b); }
              } catch (e) { desc.set.call(node, b); }
            }
          });
          return node;
        };
      }

      document.addEventListener('visibilitychange', function () {
        contexts.forEach(function (c) {
          try { if (document.hidden) c.suspend(); else c.resume(); } catch (e) { /* ignorieren */ }
        });
      });
    }
  } catch (e) { /* ignorieren */ }

  /* 5) Touch: kein Zoomen/Doppeltipp-Zoom während des Spielens (iPad/Handy). */
  try {
    document.documentElement.style.touchAction = 'manipulation';
    ['gesturestart', 'gesturechange', 'gestureend'].forEach(function (ev) {
      document.addEventListener(ev, function (e) { e.preventDefault(); }, { passive: false });
    });
  } catch (e) { /* ignorieren */ }

  /* 6) Alle übrigen Fehler nur protokollieren, nicht abstürzen lassen. */
  window.addEventListener('error', function (e) { if (window.console) console.warn('Summitbound Hinweis:', e.message); });
  window.addEventListener('unhandledrejection', function (e) { if (window.console) console.warn('Summitbound Hinweis:', e.reason); });
})();
