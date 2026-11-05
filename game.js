/* Zoo Drop - a merge-drop game. Vanilla JS + matter.js. */
(function () {
  'use strict';

  var Engine = Matter.Engine, World = Matter.World, Bodies = Matter.Bodies,
      Body = Matter.Body, Events = Matter.Events, Composite = Matter.Composite,
      Query = Matter.Query;

  // ---------- Tuning ----------
  var W = 420, H = 640;            // logical canvas size (board CSS size matches this ratio)
  var WALL = 6;                    // side margin
  var DROP_Y = 70;                 // where the held animal hangs
  var LINE_Y0 = 150;               // danger line (can be raised by the Lift power-up)
  var LIFT_STEP = 55;              // how much each Lift raises the line
  var OVER_TIME = 2500;            // ms above the line before game over
  var SETTLED_SPEED = 1.6;         // faster than this = still bouncing, does not count
  var DROP_COOLDOWN = 380;         // ms between drops
  var MAX_DROP_TIER = 4;           // only the 5 smallest animals get dropped
  var COMBO_WINDOW = 1300;         // ms between merges to keep a combo going
  var POWER_USES = { bomb: 3, boost: 2, lift: 2 };

  // Small animals are small on purpose: more fit in a row and they slip into gaps.
  var TIERS = [
    { name: 'chick',    r: 14,  color: '#f7c948' },
    { name: 'frog',     r: 18,  color: '#8bc34a' },
    { name: 'duck',     r: 23,  color: '#ffe082' },
    { name: 'penguin',  r: 29,  color: '#90a4ae' },
    { name: 'pig',      r: 36,  color: '#f8a5c2' },
    { name: 'monkey',   r: 44,  color: '#c58b5a' },
    { name: 'panda',    r: 53,  color: '#eceff1' },
    { name: 'cow',      r: 62,  color: '#d7ccc8' },
    { name: 'bear',     r: 71,  color: '#a1887f' },
    { name: 'hippo',    r: 80,  color: '#b39ddb' },
    { name: 'elephant', r: 88,  color: '#9e9e9e' }
  ];
  var SCORE = [3, 8, 15, 25, 40, 55, 70, 90, 115, 140, 170];
  var TOP_BONUS = 1000;
  var COMBO_STEP = 0.5, COMBO_MAX = 3;   // x1, x1.5, x2 ... capped at x3            // two elephants

  // ---------- DOM ----------
  var canvas = document.getElementById('game');
  var ctx = canvas.getContext('2d');
  var elScore = document.getElementById('score');
  var elBest = document.getElementById('best');
  var elNext = document.getElementById('next-img');
  var elOverlay = document.getElementById('overlay');
  var elFinal = document.getElementById('final-score');
  var elNewBest = document.getElementById('new-best');
  var elHint = document.getElementById('hint');
  var elTargetHint = document.getElementById('target-hint');
  var elChain = document.getElementById('chain');
  var btnAgain = document.getElementById('btn-again');
  var btnMute = document.getElementById('btn-mute');
  var btnRestart = document.getElementById('btn-restart');
  var powerBtns = Array.prototype.slice.call(document.querySelectorAll('.power'));
  var stage = document.getElementById('stage');

  // ---------- State ----------
  var engine, world;
  var images = {};
  var score = 0, best = 0, newBest = false;
  var running = false, over = false;
  var pointerX = W / 2;
  var currentTier = 0, nextTier = 0;
  var lastDropAt = -1e9;
  var mergeQueue = [];
  var particles = [];
  var floaters = [];               // floating score / combo texts
  var overlayTimer = null;
  var gamesPlayed = 0;
  var muted = false;
  var sdk = null;
  var shake = 0;
  var dropped = 0;
  var lineY = LINE_Y0;
  var lineAnim = LINE_Y0;
  var combo = 0, lastMergeAt = -1e9;
  var uses = {};
  var powerMode = null;            // null | 'bomb' | 'boost'

  // ---------- Helpers ----------
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function rand(a, b) { return a + Math.random() * (b - a); }
  function animals() {
    return Composite.allBodies(world).filter(function (b) { return b.label === 'animal'; });
  }

  function loadBest() {
    try { best = parseInt(localStorage.getItem('zoodrop_best') || '0', 10) || 0; } catch (e) { best = 0; }
    try { muted = localStorage.getItem('zoodrop_muted') === '1'; } catch (e) { muted = false; }
  }
  function saveBest() { try { localStorage.setItem('zoodrop_best', String(best)); } catch (e) {} }
  function saveMuted() { try { localStorage.setItem('zoodrop_muted', muted ? '1' : '0'); } catch (e) {} }

  // ---------- Hidden rescue system ----------
  // Below ~80% full the picks are honest random. Once the player is about to lose, the game
  // quietly hands over the piece that triggers the longest merge chain, two or three times in
  // a row, so the bottom "explodes". That generosity fades out between 3 and 6 minutes, and
  // bigger pieces slowly become more common, so a long game eventually ends on its own.
  var RESCUE_FILL = 0.78;          // how full the board must be before a rescue is considered
  var RESCUE_REARM_FILL = 0.6;     // the player must get back below this to earn another rescue
  var GEN_FULL_UNTIL = 180;        // seconds of full generosity
  var GEN_ZERO_AT = 360;           // seconds after which there are no rescues at all
  var RESCUE_COOLDOWN = 25000;    // ms: a player stuck in the danger zone still gets help now and then
  var gameStart = 0, rescueArmed = true, rescueBurst = 0, lastRescueAt = -1e9;
  var stats = { rescues: 0, bestChain: 0 };

  function elapsedSec() { return (performance.now() - gameStart) / 1000; }
  function generosity() {
    var t = elapsedSec();
    return t < GEN_FULL_UNTIL ? 1 : t > GEN_ZERO_AT ? 0 : 1 - (t - GEN_FULL_UNTIL) / (GEN_ZERO_AT - GEN_FULL_UNTIL);
  }
  // 0 = empty board, 1 = touching the line
  function fillRatio() {
    var list = animals(), top = H, now = performance.now();
    for (var i = 0; i < list.length; i++) {
      if (now - list[i].born < 700) continue;          // still falling: not part of the pile yet
      var t = list[i].position.y - TIERS[list[i].tier].r;
      if (t < top) top = t;
    }
    return clamp((H - top) / (H - lineY), 0, 1);
  }
  // reachable from above = nothing sitting on top of it
  function isExposed(b, list) {
    var rb = TIERS[b.tier].r;
    for (var j = 0; j < list.length; j++) {
      var o = list[j]; if (o === b) continue;
      var ro = TIERS[o.tier].r;
      if (o.position.y < b.position.y - rb * 0.3 && Math.abs(o.position.x - b.position.x) < (rb + ro) * 0.8) return false;
    }
    return true;
  }
  // how many merges would follow if this body merged right now (rough, geometric)
  function chainLength(b, list) {
    var tier = b.tier, x = b.position.x, y = b.position.y, used = {}, len = 1;
    used[b.id] = true;
    while (tier + 1 < TIERS.length) {
      var want = tier + 1, rr = TIERS[want].r, found = null;
      for (var i = 0; i < list.length; i++) {
        var n = list[i];
        if (used[n.id] || n.tier !== want) continue;
        var dx = n.position.x - x, dy = n.position.y - y;
        if (Math.sqrt(dx * dx + dy * dy) < rr * 2 * 1.25) { found = n; break; }
      }
      if (!found) break;
      used[found.id] = true; len++;
      x = (x + found.position.x) / 2; y = (y + found.position.y) / 2; tier = want;
    }
    return len;
  }
  function bestChainTier() {
    var list = animals(), bestLen = 0, bestTier = null;
    for (var i = 0; i < list.length; i++) {
      var b = list[i];
      if (b.tier > MAX_DROP_TIER || !isExposed(b, list)) continue;
      var len = chainLength(b, list);
      if (len > bestLen || (len === bestLen && b.tier > bestTier)) { bestLen = len; bestTier = b.tier; }
    }
    if (bestLen > stats.bestChain) stats.bestChain = bestLen;
    return bestTier;
  }
  // honest random, but bigger pieces creep in as the minutes pass
  function randomTier() {
    var p = world ? clamp(elapsedSec() / 240, 0, 1) : 0;
    var w = [22 - 6 * p, 22 - 4 * p, 20, 18 + 4 * p, 18 + 6 * p];
    var r = Math.random() * 100;
    for (var i = 0; i < w.length; i++) { r -= w[i]; if (r <= 0) return i; }
    return 4;
  }
  function pickTier() {
    if (!world) return randomTier();
    var fill = fillRatio();
    if (fill < RESCUE_REARM_FILL || performance.now() - lastRescueAt > RESCUE_COOLDOWN) rescueArmed = true;
    if (rescueBurst > 0) {
      rescueBurst--;
      var k = bestChainTier();
      if (k !== null) return k;
    }
    var gen = generosity();
    if ((fill >= RESCUE_FILL || overSince) && rescueArmed && Math.random() < 0.9 * gen) {
      rescueArmed = false; lastRescueAt = performance.now();
      rescueBurst = Math.max(0, Math.round(3 * gen) - 1);
      stats.rescues++;
      var k2 = bestChainTier();
      if (k2 !== null) return k2;
    }
    return randomTier();
  }

  // ---------- Sound (synthesized, no files) ----------
  var audio = null;
  function getAudio() {
    if (!audio) {
      try { audio = new (window.AudioContext || window.webkitAudioContext)(); } catch (e) { return null; }
    }
    if (audio.state === 'suspended') audio.resume();
    return audio;
  }
  function ac() { return muted ? null : getAudio(); }
  function pop(tier, comboN) {
    var a = ac(); if (!a) return;
    var t = a.currentTime;
    var o = a.createOscillator(), g = a.createGain();
    var f = (520 - tier * 28) * Math.pow(1.06, Math.min(comboN || 1, 8) - 1);
    o.type = 'sine';
    o.frequency.setValueAtTime(f, t);
    o.frequency.exponentialRampToValueAtTime(f * 1.9, t + 0.06);
    o.frequency.exponentialRampToValueAtTime(f * 1.1, t + 0.16);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(0.35, t + 0.015);
    g.gain.exponentialRampToValueAtTime(0.0001, t + 0.22 + tier * 0.02);
    o.connect(g).connect(a.destination);
    o.start(t); o.stop(t + 0.3);
  }
  function thud() {
    var a = ac(); if (!a) return;
    var t = a.currentTime;
    var o = a.createOscillator(), g = a.createGain();
    o.type = 'triangle';
    o.frequency.setValueAtTime(180, t);
    o.frequency.exponentialRampToValueAtTime(70, t + 0.09);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(0.18, t + 0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t + 0.12);
    o.connect(g).connect(a.destination);
    o.start(t); o.stop(t + 0.15);
  }
  // ---------- Haptics ----------
  // Android: the Vibration API. iPhone: Safari has no vibration API, but toggling a
  // native switch control (iOS 18+) gives a light tick, so we flip a hidden one.
  var iosSwitch = document.getElementById('haptic-switch');
  var iosHapticOk = !!(iosSwitch && 'switch' in iosSwitch) || /iPhone|iPad/.test(navigator.userAgent);
  function tickIOS(times) {
    if (!iosHapticOk || !iosSwitch) return;
    for (var i = 0; i < times; i++) {
      setTimeout(function () { iosSwitch.click(); }, i * 70);
    }
  }
  function haptic(kind, tier) {
    if (muted) return;
    var pattern, ticks = 1;
    if (kind === 'drop') { pattern = 8; }
    else if (kind === 'merge') { pattern = 12 + (tier || 0) * 4; ticks = 1; }
    else if (kind === 'combo') { pattern = [15, 40, 15, 40, 25]; ticks = 3; }
    else if (kind === 'big') { pattern = [30, 40, 60]; ticks = 2; }
    else if (kind === 'bomb') { pattern = [50, 30, 20]; ticks = 2; }
    else if (kind === 'lift') { pattern = [10, 30, 10]; ticks = 2; }
    else if (kind === 'over') { pattern = [70, 50, 70, 50, 160]; ticks = 3; }
    else return;
    try { if (navigator.vibrate && navigator.vibrate(pattern)) return; } catch (e) {}
    tickIOS(ticks);
  }

  function boom() {
    var a = ac(); if (!a) return;
    var t = a.currentTime;
    var len = 0.35, buf = a.createBuffer(1, a.sampleRate * len, a.sampleRate), d = buf.getChannelData(0);
    for (var i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * Math.pow(1 - i / d.length, 2.2);
    var src = a.createBufferSource(), g = a.createGain(), lp = a.createBiquadFilter();
    src.buffer = buf; lp.type = 'lowpass'; lp.frequency.setValueAtTime(900, t);
    g.gain.setValueAtTime(0.5, t);
    src.connect(lp).connect(g).connect(a.destination);
    src.start(t);
  }
  function sadTune() {
    var a = ac(); if (!a) return;
    var t = a.currentTime;
    [330, 294, 262, 196].forEach(function (f, i) {
      var o = a.createOscillator(), g = a.createGain();
      o.type = 'square';
      o.frequency.setValueAtTime(f, t + i * 0.16);
      g.gain.setValueAtTime(0.0001, t + i * 0.16);
      g.gain.exponentialRampToValueAtTime(0.12, t + i * 0.16 + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0001, t + i * 0.16 + 0.15);
      o.connect(g).connect(a.destination);
      o.start(t + i * 0.16); o.stop(t + i * 0.16 + 0.18);
    });
  }

  // ---------- Adaptive background music (generated live, no files) ----------
  // Empty board: slow, soft pad and sparse music-box plucks.
  // As the board fills: tempo rises, bass gets busier, hats and kick fade in, the pad opens up.
  // Everything crossfades on an "intensity" value, so the mood never jumps.
  var music = (function () {
    var a = null, master = null, padBus = null, padFilter = null, echo = null, noiseBuf = null;
    var timer = null, nextTime = 0, step = 0, playing = false;
    var intensity = 0, target = 0, level = 0;
    var ROOT = 261.63;                                                       // C4
    var CHORDS = [[0, 4, 7, 11], [-3, 0, 4, 7], [-7, -3, 0, 4], [-5, -1, 2, 7]];  // Cmaj7 Am7 Fmaj7 G
    var CHORD_ROOTS = [0, -3, -7, -5];
    var PENTA = [0, 2, 4, 7, 9, 12, 14, 16, 19, 21, 24];                     // C major pentatonic
    var melodyIdx = 5;
    function f(semi) { return ROOT * Math.pow(2, semi / 12); }

    function setup() {
      a = getAudio(); if (!a) return false;
      if (master) return true;
      master = a.createGain(); master.gain.value = 0;
      master.connect(a.destination);
      padFilter = a.createBiquadFilter(); padFilter.type = 'lowpass'; padFilter.frequency.value = 700; padFilter.Q.value = 0.5;
      padBus = a.createGain(); padBus.gain.value = 1;
      padBus.connect(padFilter).connect(master);
      echo = a.createDelay(1.0); echo.delayTime.value = 0.34;
      var echoGain = a.createGain(); echoGain.gain.value = 0.3;
      var echoLp = a.createBiquadFilter(); echoLp.type = 'lowpass'; echoLp.frequency.value = 1800;
      echo.connect(echoLp).connect(echoGain).connect(echo);
      echoGain.connect(master);
      noiseBuf = a.createBuffer(1, a.sampleRate, a.sampleRate);
      var d = noiseBuf.getChannelData(0);
      for (var i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
      return true;
    }
    function env(g, t, peak, att, dec) {
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(peak, t + att);
      g.gain.exponentialRampToValueAtTime(0.0001, t + att + dec);
    }
    function pad(chord, t, dur) {
      for (var i = 0; i < chord.length; i++) {
        for (var k = 0; k < 2; k++) {
          var o = a.createOscillator(), g = a.createGain();
          o.type = 'triangle';
          o.frequency.value = f(chord[i]) * (k ? 1.004 : 0.996);
          env(g, t, 0.045, 0.7, dur);
          o.connect(g).connect(padBus);
          o.start(t); o.stop(t + 0.7 + dur + 0.1);
        }
      }
    }
    function pluck(semi, t, vol) {
      var o = a.createOscillator(), g = a.createGain();
      o.type = 'sine'; o.frequency.value = f(semi);
      env(g, t, vol, 0.01, 0.55);
      g.connect(master); g.connect(echo);
      o.connect(g);
      o.start(t); o.stop(t + 0.6);
      var o2 = a.createOscillator(), g2 = a.createGain();            // quiet octave on top: music-box sparkle
      o2.type = 'triangle'; o2.frequency.value = f(semi + 12);
      env(g2, t, vol * 0.22, 0.01, 0.22);
      o2.connect(g2).connect(master);
      o2.start(t); o2.stop(t + 0.3);
    }
    function bass(semi, t, vol, bright) {
      var o = a.createOscillator(), g = a.createGain(), lp = a.createBiquadFilter();
      o.type = bright ? 'square' : 'sine'; o.frequency.value = f(semi - 24);
      lp.type = 'lowpass'; lp.frequency.value = bright ? 520 : 260;
      env(g, t, vol, 0.02, 0.45);
      o.connect(lp).connect(g).connect(master);
      o.start(t); o.stop(t + 0.5);
    }
    function hat(t, vol) {
      var s = a.createBufferSource(), g = a.createGain(), hp = a.createBiquadFilter();
      s.buffer = noiseBuf; hp.type = 'highpass'; hp.frequency.value = 7000;
      env(g, t, vol, 0.005, 0.06);
      s.connect(hp).connect(g).connect(master);
      s.start(t); s.stop(t + 0.08);
    }
    function kick(t, vol) {
      var o = a.createOscillator(), g = a.createGain();
      o.type = 'sine';
      o.frequency.setValueAtTime(150, t);
      o.frequency.exponentialRampToValueAtTime(45, t + 0.12);
      env(g, t, vol, 0.005, 0.2);
      o.connect(g).connect(master);
      o.start(t); o.stop(t + 0.25);
    }
    // one step = an eighth note; 8 steps per chord, 4 chords per loop
    function scheduleStep(s, t, dur) {
      var ci = Math.floor(s / 8) % 4, chord = CHORDS[ci], root = CHORD_ROOTS[ci], x = intensity;
      if (s % 8 === 0) pad(chord, t, dur * 8);
      if (s % 8 === 0) bass(root, t, 0.18, x > 0.75);
      else if (s % 8 === 4 && x > 0.35) bass(root, t, 0.14, x > 0.75);
      else if (s % 2 === 0 && x > 0.75) bass(root + (s % 8 === 6 ? 7 : 0), t, 0.11, true);
      var onBeat = s % 2 === 0;
      var p = onBeat ? 0.45 + 0.4 * x : 0.08 + 0.55 * x;
      if (Math.random() < p) {
        melodyIdx += (Math.random() < 0.5 ? -1 : 1) * (Math.random() < 0.7 ? 1 : 2);
        if (melodyIdx < 2) melodyIdx = 3;
        if (melodyIdx > PENTA.length - 1) melodyIdx = PENTA.length - 3;
        var semi = PENTA[melodyIdx];
        if (s % 8 === 0) semi = chord[1 + Math.floor(Math.random() * 3)] + 12;   // land on a chord tone at chord changes
        pluck(semi, t, 0.11 + 0.05 * x);
      }
      if (x > 0.3 && s % 2 === 1) hat(t, 0.012 + 0.05 * (x - 0.3));
      if (x > 0.55 && s % 4 === 0) kick(t, 0.12 + 0.25 * (x - 0.55));
      if (x > 0.85 && s % 4 === 2) kick(t, 0.1);
    }
    function tick() {
      if (!a) return;
      var want = (playing && !muted && !document.hidden) ? 0.32 : 0;
      level += (want - level) * 0.12;
      master.gain.setTargetAtTime(level, a.currentTime, 0.05);
      if (!playing) return;
      intensity += (target - intensity) * 0.08;
      padFilter.frequency.setTargetAtTime(600 + 2600 * intensity, a.currentTime, 0.2);
      var bpm = 84 + 50 * intensity, stepDur = 60 / bpm / 2;
      while (nextTime < a.currentTime + 0.3) {
        if (nextTime < a.currentTime - 0.5) nextTime = a.currentTime;   // after a stall, skip ahead instead of catching up
        scheduleStep(step, nextTime, stepDur);
        nextTime += stepDur; step++;
      }
    }
    return {
      start: function () {
        if (!setup()) return;
        playing = true; step = 0; melodyIdx = 5; intensity = 0; target = 0;
        nextTime = a.currentTime + 0.1;
        if (!timer) timer = setInterval(tick, 100);
      },
      stop: function () { playing = false; },
      setTarget: function (x) { target = clamp(x, 0, 1); },
      get intensity() { return intensity; }
    };
  })();

  // ---------- CrazyGames SDK (safe when absent) ----------
  function initSDK() {
    if (!window.CrazyGames || !window.CrazyGames.SDK) return Promise.resolve();
    return window.CrazyGames.SDK.init().then(function () {
      sdk = window.CrazyGames.SDK;
    }).catch(function () { sdk = null; });
  }
  function sdkCall(path) {
    if (!sdk) return;
    try {
      var parts = path.split('.');
      var fn = sdk; for (var i = 0; i < parts.length; i++) fn = fn[parts[i]];
      if (typeof fn === 'function') fn.call(sdk[parts[0]]);
    } catch (e) {}
  }
  function maybeShowAd(then) {
    if (!sdk || gamesPlayed < 2 || gamesPlayed % 2 !== 0) { then(); return; }
    var wasMuted = muted;
    try {
      sdk.ad.requestAd('midgame', {
        adStarted: function () { muted = true; },
        adFinished: function () { muted = wasMuted; then(); },
        adError: function () { muted = wasMuted; then(); }
      });
    } catch (e) { muted = wasMuted; then(); }
  }
  // Watch an ad to get one more use of a power-up. Without the SDK (local testing) it is just granted.
  // Only a real ad platform can refill a power-up. Without one, used up means used up.
  function adsAvailable() { return !!(sdk && sdk.environment !== 'disabled'); }
  function rewardedAd(onReward) {
    if (!adsAvailable()) return;
    var wasMuted = muted;
    try {
      sdk.ad.requestAd('rewarded', {
        adStarted: function () { muted = true; },
        adFinished: function () { muted = wasMuted; onReward(); },
        adError: function () { muted = wasMuted; }
      });
    } catch (e) { muted = wasMuted; }
  }

  // ---------- Setup ----------
  function loadImages() {
    var tasks = TIERS.map(function (t) {
      return new Promise(function (res) {
        var img = new Image();
        img.onload = function () { images[t.name] = img; res(); };
        img.onerror = function () { res(); };
        img.src = 'assets/animals/' + t.name + '.png';
      });
    });
    if (document.fonts && document.fonts.load) tasks.push(document.fonts.load('700 20px Fredoka').catch(function () {}));
    return Promise.all(tasks);
  }

  function buildChain() {
    elChain.innerHTML = '';
    TIERS.forEach(function (t, i) {
      var img = document.createElement('img');
      img.src = 'assets/animals/' + t.name + '.png';
      var s = 14 + i * 1.5;
      img.style.width = s + 'px'; img.style.height = s + 'px';
      img.alt = '';
      elChain.appendChild(img);
      if (i < TIERS.length - 1) {
        var a = document.createElement('span');
        a.className = 'arrow'; a.textContent = '›';
        elChain.appendChild(a);
      }
    });
  }

  function fitStage() {
    var sw = window.innerWidth, sh = window.innerHeight;
    var s = Math.min(sw / 440, sh / 840);
    stage.style.transform = 'translate(-50%, -50%) scale(' + s + ')';
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var px = Math.round(W * dpr * s), py = Math.round(H * dpr * s);
    if (canvas.width !== px || canvas.height !== py) {
      canvas.width = px; canvas.height = py;
    }
  }

  function makeWorld() {
    engine = Engine.create({ positionIterations: 10, velocityIterations: 8 });
    engine.gravity.y = 1.35;
    world = engine.world;
    var opts = { isStatic: true, friction: 0.4, restitution: 0.05 };
    World.add(world, [
      Bodies.rectangle(W / 2, H + 30, W + 200, 60, opts),    // floor
      Bodies.rectangle(-40, H / 2, 80, H * 3, opts),         // left wall
      Bodies.rectangle(W + 40, H / 2, 80, H * 3, opts)       // right wall
    ]);
    Events.on(engine, 'collisionStart', onCollision);
  }

  function spawnAnimal(x, y, tier, extra) {
    var t = TIERS[tier];
    var b = Bodies.circle(x, y, t.r, {
      restitution: 0.12,
      friction: 0.35,
      frictionStatic: 0.6,
      frictionAir: 0.004,
      density: 0.0022 + tier * 0.0003,
      label: 'animal'
    });
    b.tier = tier;
    b.born = performance.now();
    b.overSince = 0;
    b.popIn = extra && extra.popIn ? performance.now() : 0;
    b.merging = false;
    World.add(world, b);
    return b;
  }

  function onCollision(ev) {
    var pairs = ev.pairs;
    for (var i = 0; i < pairs.length; i++) {
      var a = pairs[i].bodyA, b = pairs[i].bodyB;
      if (a.label !== 'animal' || b.label !== 'animal') {
        if ((a.label === 'animal' || b.label === 'animal') && !over) {
          var an = a.label === 'animal' ? a : b;
          if (performance.now() - an.born < 900 && Math.abs(an.velocity.y) > 4) thud();
        }
        continue;
      }
      if (a.tier !== b.tier || a.merging || b.merging) continue;
      a.merging = b.merging = true;
      mergeQueue.push([a, b]);
    }
  }

  function addScore(base, x, y) {
    x = clamp(x, 70, W - 70);   // keep the floating text inside the board
    var now = performance.now();
    combo = (now - lastMergeAt < COMBO_WINDOW) ? combo + 1 : 1;
    lastMergeAt = now;
    var gained = Math.round(base * Math.min(COMBO_MAX, 1 + COMBO_STEP * (combo - 1)));
    score += gained;
    floaters.push({ x: x, y: y - 10, text: '+' + gained, life: 1, size: 20 + Math.min(combo, 6) * 2, color: '#3f2d20' });
    if (combo >= 2) {
      floaters.push({ x: x, y: y - 40, text: 'COMBO x' + combo, life: 1.2, size: 22 + Math.min(combo, 8) * 2, color: '#e8604c' });
      if (combo >= 3) shake = Math.max(shake, 3 + combo);
    }
    if (score > best) { best = score; newBest = true; saveBest(); }
    updateHud();
    return combo;
  }

  function processMerges() {
    while (mergeQueue.length) {
      var pr = mergeQueue.shift();
      var a = pr[0], b = pr[1];
      if (!Composite.get(world, a.id, 'body') || !Composite.get(world, b.id, 'body')) continue;
      var tier = a.tier;
      var x = (a.position.x + b.position.x) / 2, y = (a.position.y + b.position.y) / 2;
      var vx = (a.velocity.x + b.velocity.x) / 2, vy = (a.velocity.y + b.velocity.y) / 2;
      World.remove(world, a); World.remove(world, b);
      evolveAt(x, y, tier, vx, vy);
    }
  }

  // shared by merges and the Upgrade power-up
  function evolveAt(x, y, tier, vx, vy) {
    burst(x, y, TIERS[tier].color, 10 + tier * 2, TIERS[tier].r);
    if (tier + 1 < TIERS.length) {
      var c = addScore(SCORE[tier], x, y);
      pop(tier, c);
      haptic(c >= 3 ? 'combo' : 'merge', tier);
      var nb = spawnAnimal(x, y, tier + 1, { popIn: true });
      Body.setVelocity(nb, { x: (vx || 0) * 0.5, y: Math.min((vy || 0) * 0.5, 0) });
    } else {
      addScore(TOP_BONUS, x, y);
      pop(tier, 8);
      haptic('big');
      shake = 12;
      burst(x, y, '#f7c948', 40, 90);
    }
  }

  function burst(x, y, color, n, r) {
    for (var i = 0; i < n; i++) {
      var ang = rand(0, Math.PI * 2), sp = rand(1.5, 4.5) + r / 60;
      particles.push({
        x: x + Math.cos(ang) * r * 0.4, y: y + Math.sin(ang) * r * 0.4,
        vx: Math.cos(ang) * sp, vy: Math.sin(ang) * sp - 1.5,
        life: 1, size: rand(3, 7), color: color
      });
    }
  }

  // ---------- Power-ups ----------
  function resetPowers() {
    uses = { bomb: POWER_USES.bomb, boost: POWER_USES.boost, lift: POWER_USES.lift };
    setPowerMode(null);
    renderPowers();
  }
  function renderPowers() {
    powerBtns.forEach(function (btn) {
      var k = btn.getAttribute('data-power'), n = uses[k] || 0;
      var c = btn.querySelector('.count');
      c.textContent = n > 0 ? n : (adsAvailable() ? 'AD' : '0');
      c.classList.toggle('ad', n === 0 && adsAvailable());
      btn.classList.toggle('empty', n === 0);
      btn.classList.toggle('active', powerMode === k);
    });
  }
  function setPowerMode(mode) {
    powerMode = mode;
    elTargetHint.classList.toggle('hidden', !mode);
    renderPowers();
  }
  function usePower(k) {
    if (!running || over) return;
    if (uses[k] <= 0) {
      rewardedAd(function () { uses[k] = (uses[k] || 0) + 1; renderPowers(); });
      return;
    }
    if (k === 'lift') {
      uses.lift--;
      lineY = Math.max(40, lineY - LIFT_STEP);
      floaters.push({ x: W / 2, y: lineY + 30, text: 'LINE UP!', life: 1.2, size: 26, color: '#4f8a2c' });
      pop(2, 3);
      haptic('lift');
      renderPowers();
      return;
    }
    setPowerMode(powerMode === k ? null : k);
  }
  function applyPowerAt(px, py) {
    var hits = Query.point(animals(), { x: px, y: py });
    var mode = powerMode;
    setPowerMode(null);
    if (!hits.length) return;
    var b = hits[0], x = b.position.x, y = b.position.y, tier = b.tier;
    if (mode === 'bomb') {
      uses.bomb--;
      World.remove(world, b);
      burst(x, y, '#3f2d20', 18, TIERS[tier].r);
      burst(x, y, '#e8604c', 12, TIERS[tier].r);
      shake = 9;
      boom();
      haptic('bomb');
    } else if (mode === 'boost') {
      uses.boost--;
      World.remove(world, b);
      evolveAt(x, y, tier, 0, 0);
    }
    renderPowers();
  }

  // ---------- Game flow ----------
  function newGame() {
    if (engine) { Events.off(engine); World.clear(world, false); Engine.clear(engine); }
    makeWorld();
    score = 0; newBest = false; over = false; running = true;
    particles.length = 0; floaters.length = 0; mergeQueue.length = 0; dropped = 0;
    lastDropAt = -1e9; combo = 0; lastMergeAt = -1e9;
    lineY = LINE_Y0; lineAnim = LINE_Y0; overSince = 0; dangerIds = {};
    gameStart = performance.now(); rescueArmed = true; rescueBurst = 0; lastRescueAt = -1e9; stats.rescues = 0; stats.bestChain = 0;
    currentTier = randomTier(); nextTier = randomTier();
    resetPowers();
    elOverlay.classList.add('hidden');
    elHint.classList.remove('hidden');
    updateHud();
    music.start();
    sdkCall('game.gameplayStart');
  }

  function drop() {
    if (!running || over) return;
    var now = performance.now();
    if (now - lastDropAt < DROP_COOLDOWN) return;
    lastDropAt = now;
    var t = TIERS[currentTier];
    var x = clamp(pointerX, WALL + t.r + 2, W - WALL - t.r - 2);
    spawnAnimal(x, DROP_Y, currentTier);
    haptic('drop');
    combo = 0; lastMergeAt = -1e9;   // a combo is one drop's chain reaction, not fast tapping
    currentTier = nextTier; nextTier = pickTier();
    dropped++;
    if (dropped >= 2) elHint.classList.add('hidden');
    updateHud();
  }

  function gameOver() {
    if (over) return;
    over = true; running = false;
    gamesPlayed++;
    shake = 14;
    sadTune();
    haptic('over');
    music.stop();
    setPowerMode(null);
    sdkCall('game.gameplayStop');
    if (newBest) sdkCall('game.happytime');
    elFinal.textContent = score;
    elNewBest.classList.toggle('hidden', !newBest);
    clearTimeout(overlayTimer);
    overlayTimer = setTimeout(function () { elOverlay.classList.remove('hidden'); }, 700);
  }

  var overSince = 0;   // when something settled first poked above the line (0 = nothing is)
  var dangerIds = {};  // bodies currently poking above the line (drawn with a red ring)
  function checkGameOver(now) {
    var list = animals(), anyOver = false;
    dangerIds = {};
    for (var i = 0; i < list.length; i++) {
      var b = list[i];
      var top = b.position.y - TIERS[b.tier].r;
      if (now - b.born > 700 && top < lineY - 6 && b.speed < SETTLED_SPEED) { anyOver = true; dangerIds[b.id] = true; }
    }
    if (!anyOver) { overSince = 0; return; }
    if (!overSince) overSince = now;
    else if (now - overSince > OVER_TIME) gameOver();
  }

  function updateHud() {
    elScore.textContent = score;
    elBest.textContent = best;
    elNext.src = 'assets/animals/' + TIERS[nextTier].name + '.png';
  }

  // ---------- Render ----------
  function drawAnimal(b, now) {
    var t = TIERS[b.tier];
    var img = images[t.name];
    var sc = 1;
    if (b.popIn) {
      var p = (now - b.popIn) / 260;
      if (p >= 1) { b.popIn = 0; }
      else { sc = 0.55 + 0.45 * (1 - Math.pow(1 - p, 3)) + Math.sin(p * Math.PI) * 0.18; }
    }
    ctx.save();
    ctx.translate(b.position.x, b.position.y);
    ctx.rotate(b.angle);
    ctx.scale(sc, sc);
    if (img) {
      var d = t.r * 2.08;
      var ar = img.width / img.height;
      var dw = ar >= 1 ? d : d * ar, dh = ar >= 1 ? d / ar : d;
      ctx.drawImage(img, -dw / 2, -dh / 2, dw, dh);
    } else {
      ctx.fillStyle = t.color; ctx.beginPath(); ctx.arc(0, 0, t.r, 0, Math.PI * 2); ctx.fill();
    }
    ctx.restore();
  }

  function render(now) {
    var s = canvas.width / W;
    ctx.setTransform(s, 0, 0, s, 0, 0);
    ctx.clearRect(0, 0, W, H);

    var sx = 0, sy = 0;
    if (shake > 0) { sx = rand(-shake, shake) * 0.5; sy = rand(-shake, shake) * 0.5; shake *= 0.86; if (shake < 0.3) shake = 0; }
    ctx.translate(sx, sy);

    // danger line eases to its position when lifted
    lineAnim += (lineY - lineAnim) * 0.15;
    ctx.save();
    ctx.strokeStyle = '#e8604c';
    ctx.lineWidth = 3;
    ctx.setLineDash([10, 9]);
    ctx.globalAlpha = 0.75;
    ctx.beginPath(); ctx.moveTo(10, lineAnim); ctx.lineTo(W - 10, lineAnim); ctx.stroke();
    ctx.restore();

    // ground stripe
    ctx.fillStyle = '#f0c892';
    ctx.fillRect(0, H - 10, W, 10);

    // held animal + guide
    if (running && !over && !powerMode) {
      var t = TIERS[currentTier];
      var hx = clamp(pointerX, WALL + t.r + 2, W - WALL - t.r - 2);
      ctx.save();
      ctx.strokeStyle = 'rgba(63,45,32,0.18)';
      ctx.lineWidth = 2; ctx.setLineDash([4, 8]);
      ctx.beginPath(); ctx.moveTo(hx, DROP_Y + t.r); ctx.lineTo(hx, H - 10); ctx.stroke();
      ctx.restore();
      var ready = now - lastDropAt >= DROP_COOLDOWN;
      var bob = Math.sin(now / 260) * 3;
      var fake = { position: { x: hx, y: DROP_Y + bob }, angle: 0, tier: currentTier, popIn: ready ? 0 : lastDropAt };
      ctx.save(); ctx.globalAlpha = ready ? 1 : 0.5;
      drawAnimal(fake, now);
      ctx.restore();
    }

    // bodies
    var list = animals();
    for (var i = 0; i < list.length; i++) drawAnimal(list[i], now);
    if (overSince || over) {
      for (var q = 0; q < list.length; q++) {
        var db = list[q];
        if (!dangerIds[db.id]) continue;
        ctx.save();
        ctx.globalAlpha = over ? 0.95 : 0.55 + 0.45 * Math.abs(Math.sin(now / 120));
        ctx.strokeStyle = '#e8604c';
        ctx.lineWidth = 5;
        ctx.setLineDash([]);
        ctx.beginPath(); ctx.arc(db.position.x, db.position.y, TIERS[db.tier].r + 5, 0, Math.PI * 2); ctx.stroke();
        ctx.restore();
      }
    }

    // targeting mode: dim everything a little and pulse
    if (powerMode) {
      ctx.save();
      ctx.globalAlpha = 0.12 + 0.06 * Math.sin(now / 150);
      ctx.fillStyle = powerMode === 'bomb' ? '#e8604c' : '#f7c948';
      ctx.fillRect(0, 0, W, H);
      ctx.restore();
    }

    // warning glow when someone is near the line
    if (!over) {
      var danger = overSince ? (now - overSince) / OVER_TIME : 0;
      if (danger > 0) {
        ctx.save();
        ctx.globalAlpha = 0.25 + 0.35 * Math.abs(Math.sin(now / 90)) * danger;
        ctx.fillStyle = '#e8604c';
        ctx.fillRect(0, 0, W, lineAnim);
        ctx.restore();
      }
    }

    // particles
    for (var k = particles.length - 1; k >= 0; k--) {
      var p = particles[k];
      p.x += p.vx; p.y += p.vy; p.vy += 0.18; p.vx *= 0.97; p.life -= 0.028;
      if (p.life <= 0) { particles.splice(k, 1); continue; }
      ctx.save();
      ctx.globalAlpha = Math.max(0, p.life);
      ctx.fillStyle = p.color;
      ctx.strokeStyle = '#3f2d20'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(p.x, p.y, p.size * p.life, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
      ctx.restore();
    }

    // floating texts
    for (var m = floaters.length - 1; m >= 0; m--) {
      var f = floaters[m];
      f.y -= 0.9; f.life -= 0.018;
      if (f.life <= 0) { floaters.splice(m, 1); continue; }
      ctx.save();
      ctx.globalAlpha = Math.min(1, f.life * 1.5);
      ctx.font = '700 ' + f.size + 'px Fredoka, "Trebuchet MS", sans-serif';
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.lineWidth = 5; ctx.lineJoin = 'round';
      ctx.strokeStyle = '#fff9ea';
      ctx.strokeText(f.text, f.x, f.y);
      ctx.fillStyle = f.color;
      ctx.fillText(f.text, f.x, f.y);
      ctx.restore();
    }
  }

  // ---------- Loop ----------
  var last = 0, acc = 0, STEP = 1000 / 60;
  function frame(now) {
    requestAnimationFrame(frame);
    if (!last) last = now;
    var dt = Math.min(now - last, 100); last = now;
    if (!over) {
      acc += dt;
      while (acc >= STEP) { Engine.update(engine, STEP); acc -= STEP; }
      processMerges();
      if (running) {
        checkGameOver(now);
        music.setTarget(overSince ? 1 : (fillRatio() - 0.12) / 0.7);
      }
    }
    render(now);
  }

  // ---------- Input ----------
  function toLogical(e) {
    var r = canvas.getBoundingClientRect();
    return { x: (e.clientX - r.left) / r.width * W, y: (e.clientY - r.top) / r.height * H };
  }
  var pressing = false;
  canvas.addEventListener('pointerdown', function (e) {
    pressing = true; pointerX = toLogical(e).x; ac();
    e.preventDefault();
  });
  canvas.addEventListener('pointermove', function (e) {
    if (e.pointerType === 'mouse' || pressing) pointerX = toLogical(e).x;
  });
  canvas.addEventListener('pointerup', function (e) {
    if (!pressing) return;
    pressing = false;
    var p = toLogical(e);
    pointerX = p.x;
    if (powerMode) { applyPowerAt(p.x, p.y); return; }
    drop();
  });
  canvas.addEventListener('pointercancel', function () { pressing = false; });
  window.addEventListener('keydown', function (e) {
    if (e.code === 'Space' || e.code === 'ArrowDown') { drop(); e.preventDefault(); }
    if (e.code === 'ArrowLeft') pointerX = clamp(pointerX - 14, 0, W);
    if (e.code === 'ArrowRight') pointerX = clamp(pointerX + 14, 0, W);
    if (e.code === 'Escape') setPowerMode(null);
  });

  powerBtns.forEach(function (btn) {
    btn.addEventListener('click', function () { usePower(btn.getAttribute('data-power')); });
  });
  btnAgain.addEventListener('click', function () { maybeShowAd(newGame); });
  btnRestart.addEventListener('click', function () {
    if (over) { maybeShowAd(newGame); return; }
    newGame();
  });
  function renderMute() { btnMute.classList.toggle('off', muted); }
  btnMute.addEventListener('click', function () { muted = !muted; saveMuted(); renderMute(); });

  window.addEventListener('resize', fitStage);
  document.addEventListener('visibilitychange', function () { last = 0; acc = 0; });

  // ---------- Boot ----------
  loadBest();
  renderMute();
  buildChain();
  fitStage();
  initSDK().then(function () {
    sdkCall('game.loadingStart');
    return loadImages();
  }).then(function () {
    sdkCall('game.loadingStop');
    fitStage();
    newGame();
    requestAnimationFrame(frame);
  });
})();
