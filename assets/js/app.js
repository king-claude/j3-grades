/* ==========================================================================
   九三班成绩发布页 · 交互逻辑
   - 姓名精确匹配（自动忽略空格 / 全角半角 / 大小写差异）
   - 未命中时按相似度推荐候选姓名
   - 姓名 + 密码查询；首次成功后绑定本机，其他姓名无效
   - 总分、等级由前端实时计算；按老师要求不显示班级排名、单科排名和班级均分
   ========================================================================== */
(function () {
  "use strict";

  /* ----------------------------- 基础工具 ----------------------------- */

  var $ = function (sel, root) { return (root || document).querySelector(sel); };

  function esc(str) {
    return String(str == null ? "" : str).replace(/[&<>"']/g, function (c) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c];
    });
  }

  // 姓名归一化：全角→半角、去掉空格与间隔号、转小写
  function normName(str) {
    var s = String(str == null ? "" : str);
    if (s.normalize) s = s.normalize("NFKC");
    return s.replace(/[\s\u3000·•・.。`'’\-—_]/g, "").toLowerCase();
  }

  function toNumber(v) {
    if (v === null || v === undefined || v === "") return null;
    if (typeof v === "number") return isFinite(v) ? v : null;
    var s = String(v).replace(/[^\d.\-]/g, "");
    if (s === "" || s === "." || s === "-") return null;
    var n = Number(s);
    return isFinite(n) ? n : null;
  }

  function fmt(n) {
    if (n === null || n === undefined || isNaN(n)) return "—";
    return Math.abs(n - Math.round(n)) < 1e-9 ? String(Math.round(n)) : n.toFixed(1);
  }

  function signed(n) {
    var s = fmt(Math.abs(n));
    return (n > 0 ? "+" : n < 0 ? "−" : "±") + s;
  }

  function clamp(n, min, max) { return Math.min(max, Math.max(min, n)); }

  function prefersReducedMotion() {
    return window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  }

  /* ----------------------------- 口令校验（SHA-256 KDF） -----------------------------
     纯 JS 实现，不依赖 WebCrypto —— 局域网 http 和手机浏览器都能正常校验。
     算法与 tools/excel_to_grades.py 完全一致：
       h = sha256(salt + ":" + password)；再连续 sha256(h) 若干轮后取 hex。
     ---------------------------------------------------------------------------------- */

  function utf8Encode(str) {
    if (typeof TextEncoder !== "undefined") return new TextEncoder().encode(str);
    var out = [], i, c;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 63));
      else out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
    }
    return new Uint8Array(out);
  }

  var SHA256_K = (function () {
    var k = [], composite = {};
    for (var c = 2; k.length < 64; c++) {
      if (!composite[c]) {
        for (var m = c * c; m < 320; m += c) composite[m] = true;
        k.push((Math.pow(c, 1 / 3) * 4294967296) | 0);
      }
    }
    return k;
  })();

  function rotr(x, n) { return (x >>> n) | (x << (32 - n)); }

  function hex32(x) { return ("00000000" + (x >>> 0).toString(16)).slice(-8); }

  function sha256Hex(str) {
    var bytes = utf8Encode(str);
    var total = (((bytes.length + 8) >> 6) + 1) << 6;
    var buf = new Uint8Array(total);
    buf.set(bytes);
    buf[bytes.length] = 0x80;

    var view = new DataView(buf.buffer);
    var bits = bytes.length * 8;
    view.setUint32(total - 8, Math.floor(bits / 4294967296));
    view.setUint32(total - 4, bits >>> 0);

    var h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a,
        h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;
    var w = new Uint32Array(64);

    for (var off = 0; off < total; off += 64) {
      for (var i = 0; i < 16; i++) w[i] = view.getUint32(off + i * 4);
      for (i = 16; i < 64; i++) {
        var x = w[i - 15], y = w[i - 2];
        var s0 = (rotr(x, 7) ^ rotr(x, 18) ^ (x >>> 3)) >>> 0;
        var s1 = (rotr(y, 17) ^ rotr(y, 19) ^ (y >>> 10)) >>> 0;
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) >>> 0;
      }

      var a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7;

      for (i = 0; i < 64; i++) {
        var S1 = (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) >>> 0;
        var ch = ((e & f) ^ (~e & g)) >>> 0;
        var t1 = (h + S1 + ch + SHA256_K[i] + w[i]) >>> 0;
        var S0 = (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) >>> 0;
        var maj = ((a & b) ^ (a & c) ^ (b & c)) >>> 0;
        var t2 = (S0 + maj) >>> 0;
        h = g; g = f; f = e; e = (d + t1) >>> 0;
        d = c; c = b; b = a; a = (t1 + t2) >>> 0;
      }

      h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0;
      h4 = (h4 + e) >>> 0; h5 = (h5 + f) >>> 0; h6 = (h6 + g) >>> 0; h7 = (h7 + h) >>> 0;
    }

    return hex32(h0) + hex32(h1) + hex32(h2) + hex32(h3) +
           hex32(h4) + hex32(h5) + hex32(h6) + hex32(h7);
  }

  function kdfHex(password, salt, rounds) {
    var h = sha256Hex(salt + ":" + password);
    for (var i = 0; i < rounds; i++) h = sha256Hex(h);
    return h;
  }

  function normalizePassword(pw) {
    var s = String(pw == null ? "" : pw).trim();
    if (s.normalize) s = s.normalize("NFKC"); // 全角数字 → 半角
    return s.toLowerCase();
  }

  /* ----------------------------- 数据整理 ----------------------------- */

  var LEVELS = [
    { min: 0.85, label: "优秀",   color: "#059669", color2: "#6ee7b7", bg: "#ecfdf5" },
    { min: 0.70, label: "良好",   color: "#2563eb", color2: "#93c5fd", bg: "#eff6ff" },
    { min: 0.60, label: "及格",   color: "#d97706", color2: "#fcd34d", bg: "#fffbeb" },
    { min: -Infinity, label: "待提高", color: "#dc2626", color2: "#fca5a5", bg: "#fef2f2" }
  ];

  function levelOf(rate) {
    for (var i = 0; i < LEVELS.length; i++) if (rate >= LEVELS[i].min) return LEVELS[i];
    return LEVELS[LEVELS.length - 1];
  }

  function normalizeData(raw) {
    var meta = raw.meta || {};
    var fullMarks = raw.fullMarks || {};

    var subjects = (raw.subjects || []).map(function (s) {
      if (typeof s === "string") {
        return { name: s, full: toNumber(fullMarks[s]) || 100 };
      }
      var name = String(s.name || "").trim();
      var full = toNumber(s.full);
      if (!full) full = toNumber(fullMarks[name]) || 100;
      return { name: name, full: full };
    }).filter(function (s) { return s.name; });

    var students = (raw.students || []).map(function (st) {
      var scores = {};
      var src = st.scores || {};
      Object.keys(src).forEach(function (k) { scores[String(k).trim()] = toNumber(src[k]); });

      var bySubject = {};
      var total = 0;
      var scored = 0;
      subjects.forEach(function (sub) {
        var v = scores[sub.name];
        if (v === null || v === undefined) v = null;
        bySubject[sub.name] = v;
        if (v !== null) { total += v; scored += 1; }
      });

      return {
        name: String(st.name || "").trim(),
        aliases: Array.isArray(st.aliases)
          ? st.aliases.map(function (a) { return String(a).trim(); }).filter(Boolean)
          : [],
        raw: scores,
        bySubject: bySubject,
        total: scored > 0 ? Math.round(total * 10) / 10 : null,
        scoredCount: scored,
        auth: (st.auth && st.auth.salt && st.auth.hash) ? {
          salt: String(st.auth.salt),
          hash: String(st.auth.hash),
          rounds: toNumber(st.auth.rounds) || null
        } : null
      };
    }).filter(function (st) { return st.name; });

    return {
      meta: {
        className: meta.className || "九三班",
        gradeName: meta.gradeName || "九年级三班",
        examName: meta.examName || "本次考试",
        updatedAt: meta.updatedAt || "",
        isSample: !!meta.isSample,
        lockMinutes: toNumber(meta.lockMinutes) === null ? 720 : toNumber(meta.lockMinutes),
        authRounds: toNumber(meta.authRounds) || 5000,
        passwordHint: meta.passwordHint || "学号后 6 位",
        passwordInput: meta.passwordInput === "numeric" || meta.passwordInput === "text" ? meta.passwordInput : "",
        requirePassword: meta.requirePassword !== false
      },
      subjects: subjects,
      students: students
    };
  }

  // 并列名次：同分同名次，下一名次顺延
  function rankOf(list, getValue) {
    var rows = list.map(function (item, i) {
      return { item: item, i: i, v: getValue(item) };
    }).filter(function (r) { return typeof r.v === "number" && !isNaN(r.v); });

    rows.sort(function (a, b) { return b.v - a.v || a.i - b.i; });

    var map = new Map();
    var lastV = null, lastRank = 0;
    rows.forEach(function (r, idx) {
      var rank = (lastV !== null && Math.abs(r.v - lastV) < 1e-9) ? lastRank : idx + 1;
      map.set(r.item, rank);
      lastV = r.v; lastRank = rank;
    });
    return { map: map, count: rows.length };
  }

  /* ----------------------------- 应用状态 ----------------------------- */

  var DATA = null;
  var INDEX = null; // 计算后的统计索引
  var authRequired = false;   // 是否启用查询密码
  var passwordHint = "";      // 密码说明，如“学号后 6 位”

  // 本机锁定：同一台设备第一次查到成绩后，只允许重复查看这个人
  var LOCK_KEY = "j3-grade-lock-v1";
  var lockMinutes = 0;  // 0 = 不启用锁定
  var lockInfo = null;  // { name, exp, at }

  function buildIndex(data) {
    var subjects = data.subjects;
    var students = data.students;

    var totalRank = rankOf(students, function (s) { return s.total; });

    var perSubject = {};
    subjects.forEach(function (sub) {
      var values = students
        .map(function (s) { return s.bySubject[sub.name]; })
        .filter(function (v) { return typeof v === "number"; });

      var sum = values.reduce(function (a, b) { return a + b; }, 0);
      var ranks = rankOf(students, function (s) { return s.bySubject[sub.name]; });

      perSubject[sub.name] = {
        avg: values.length ? sum / values.length : null,
        max: values.length ? Math.max.apply(null, values) : null,
        min: values.length ? Math.min.apply(null, values) : null,
        count: values.length,
        ranks: ranks.map
      };
    });

    var totalSum = 0, totalCount = 0;
    students.forEach(function (s) {
      if (typeof s.total === "number") { totalSum += s.total; totalCount += 1; }
    });

    return {
      totalRank: totalRank,
      perSubject: perSubject,
      avgTotal: totalCount ? totalSum / totalCount : null,
      fullTotal: subjects.reduce(function (a, s) { return a + s.full; }, 0)
    };
  }

  /* ----------------------------- 本机锁定 ----------------------------- */

  function readLock() {
    try {
      var raw = window.localStorage.getItem(LOCK_KEY);
      if (raw) {
        var obj = JSON.parse(raw);
        if (obj && obj.name && obj.exp) {
          if (Date.now() > obj.exp) {
            window.localStorage.removeItem(LOCK_KEY);
          } else {
            return obj;
          }
        }
      }
    } catch (err) {
      /* 隐私模式 / file:// 下存储不可用时，退回内存锁定 */
    }

    if (lockInfo) {
      if (Date.now() > lockInfo.exp) { lockInfo = null; return null; }
      return lockInfo;
    }
    return null;
  }

  function writeLock(name) {
    var obj = { name: name, at: Date.now(), exp: Date.now() + lockMinutes * 60000 };
    try { window.localStorage.setItem(LOCK_KEY, JSON.stringify(obj)); } catch (err) { /* 隐私模式等环境忽略 */ }
    lockInfo = obj;
    return obj;
  }

  function dropLock() {
    try { window.localStorage.removeItem(LOCK_KEY); } catch (err) { /* ignore */ }
    lockInfo = null;
  }

  function pad2(n) { return n < 10 ? "0" + n : "" + n; }

  function formatLockTime(ts) {
    var d = new Date(ts);
    return (d.getMonth() + 1) + "月" + d.getDate() + "日 " + pad2(d.getHours()) + ":" + pad2(d.getMinutes());
  }

  function verifyPassword(student, password) {
    if (!student || !student.auth) return false;
    var rounds = student.auth.rounds || DATA.meta.authRounds || 5000;
    return kdfHex(normalizePassword(password), student.auth.salt, rounds) === student.auth.hash;
  }

  // 锁定后：密码框禁用，顶部显示“已绑定 张三”
  function applyLockedUI(lock) {
    var pw = $("#pwInput");
    if (pw) {
      pw.value = "";
      pw.disabled = true;
      pw.placeholder = "本机已绑定，无需密码";
    }
    var toggle = $("#pwToggle");
    if (toggle) toggle.hidden = true;
    var tip = $("#pwTip");
    if (tip) tip.textContent = "已绑定";
    var badge = $("#lockBadge");
    if (badge) { badge.textContent = "已绑定 " + lock.name; badge.hidden = false; }
  }

  function clearLockedUI() {
    var pw = $("#pwInput");
    if (pw) {
      pw.disabled = false;
      pw.placeholder = "请输入密码";
      pw.value = "";
    }
    var toggle = $("#pwToggle");
    if (toggle) toggle.hidden = false;
    var tip = $("#pwTip");
    if (tip) tip.textContent = passwordHint;
    var badge = $("#lockBadge");
    if (badge) badge.hidden = true;
  }

  /* ----------------------------- 渲染：成绩单 ----------------------------- */

  function subjectCard(sub, student, idx) {
    var value = student.bySubject[sub.name];
    var rate = value === null ? 0 : clamp(value / sub.full, 0, 1);
    var lv = levelOf(rate);

    return '' +
      '<div class="subject-card" style="--i:' + idx + ';--level-color:' + lv.color +
        ';--level-color-2:' + lv.color2 + ';--level-bg:' + lv.bg + '">' +
        '<div class="sc-head">' +
          '<span class="sc-name">' + esc(sub.name) + '</span>' +
          '<span class="sc-level">' + (value === null ? "缺考" : lv.label) + '</span>' +
        '</div>' +
        '<div class="sc-body">' +
          '<span class="sc-score">' + (value === null ? "—" : fmt(value)) + '</span>' +
          '<span class="sc-full">/ ' + fmt(sub.full) + '</span>' +
        '</div>' +
        '<div class="bar"><span style="--w:' + (rate * 100).toFixed(1) + '%"></span></div>' +
        (value === null ? "" :
          '<div class="sc-foot"><span class="sc-rate">得分率 ' + Math.round(rate * 100) + '%</span></div>'
        ) +
      '</div>';
  }

  function renderReport(student, lock) {
    var idx = INDEX;

    // 按得分率找出相对优势 / 相对薄弱科目
    var rated = DATA.subjects.map(function (sub) {
      var v = student.bySubject[sub.name];
      return { sub: sub, v: v, rate: v === null ? null : v / sub.full };
    }).filter(function (r) { return r.rate !== null; });
    rated.sort(function (a, b) { return b.rate - a.rate; });

    var best = rated[0] || null;
    var worst = rated.length > 1 ? rated[rated.length - 1] : null;

    var pills = [];
    if (student.total !== null && idx.fullTotal) {
      pills.push('<span class="pill is-cool">得分率 ' +
        Math.round(student.total / idx.fullTotal * 100) + '%</span>');
    }
    if (best) {
      pills.push('<span class="pill">相对优势 ' + esc(best.sub.name) + ' ' + fmt(best.v) +
        '<span class="pill-sub">/' + fmt(best.sub.full) + '</span></span>');
    }
    if (worst && worst.sub.name !== best.sub.name) {
      pills.push('<span class="pill">相对薄弱 ' + esc(worst.sub.name) + ' ' + fmt(worst.v) +
        '<span class="pill-sub">/' + fmt(worst.sub.full) + '</span></span>');
    }
    if (student.scoredCount < DATA.subjects.length) {
      pills.push('<span class="pill is-warn">有 ' + (DATA.subjects.length - student.scoredCount) + ' 科缺考</span>');
    }
    if (lock) {
      pills.push('<span class="pill is-cool">本机已锁定 · ' + formatLockTime(lock.exp) + ' 后解除</span>');
    }

    var cards = DATA.subjects.map(function (sub, i) {
      return subjectCard(sub, student, i);
    }).join("");

    return '' +
      '<article class="report" id="reportCard">' +
        '<div class="report-head">' +
          '<div class="who">' +
            '<span class="label">本次成绩</span>' +
            '<span class="student-name">' + esc(student.name) + '</span>' +
            '<span class="student-meta">' + esc(DATA.meta.gradeName) + ' · ' + esc(DATA.meta.examName) + '</span>' +
          '</div>' +
          '<div class="score-total">' +
            '<span class="label">总分</span>' +
            '<span class="total-value" id="totalValue" data-total="' + (student.total === null ? "" : student.total) + '">' +
              (student.total === null ? "—" : "0") +
            '</span>' +
            '<span class="total-full">/ ' + fmt(idx.fullTotal) + '</span>' +
          '</div>' +
        '</div>' +
        '<div class="pills">' + pills.join("") + '</div>' +
        '<div class="subject-grid">' + cards + '</div>' +
        '<div class="report-actions">' +
          '<button type="button" class="btn btn-ghost" id="printBtn">' +
            '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">' +
              '<path d="M6 9V3h12v6"></path><path d="M6 18H4a2 2 0 0 1-2-2v-4a2 2 0 0 1 2-2h16a2 2 0 0 1 2 2v4a2 2 0 0 1-2 2h-2"></path>' +
              '<rect x="6" y="14" width="12" height="8" rx="1"></rect></svg>' +
            '<span>打印 / 保存 PDF</span>' +
          '</button>' +
          (lock ? "" :
            '<button type="button" class="btn btn-ghost" id="againBtn">查询其他同学</button>'
          ) +
          '<p class="report-note">满分合计 ' + fmt(idx.fullTotal) + ' 分 · 等级按得分率划分' +
            (lock ? ' · 本机仅限查询本人' : '') + '</p>' +
        '</div>' +
      '</article>';
  }

  /* ----------------------------- 渲染：未找到 ----------------------------- */

  function renderNotFound(query) {
    var suggested = similarNames(query);
    var chips = suggested.map(function (n) {
      return '<button type="button" class="chip" data-name="' + esc(n) + '">' + esc(n) + '</button>';
    }).join("");

    return '' +
      '<div class="not-found-card" role="alert">' +
        '<span class="nf-ico" aria-hidden="true">?</span>' +
        '<h2 class="nf-title">没有找到「' + esc(query) + '」的成绩</h2>' +
        '<p class="nf-text">' + (suggested.length
          ? "可能是姓名写法不同，试试下面这些同学："
          : "请确认姓名是否与学籍一致。若名单里确实没有你，请联系班主任核对录入情况。") +
        '</p>' +
        (chips ? '<div class="nf-chips">' + chips + '</div>' : "") +
      '</div>';
  }

  // 相似姓名：包含关系 / 公共字 / 编辑距离
  function similarNames(query) {
    var q = normName(query);
    if (!q) return [];

    var scored = DATA.students.map(function (s) {
      var n = normName(s.name);
      var score = 0;
      if (n === q) score = 1;
      else if (n.indexOf(q) >= 0 || q.indexOf(n) >= 0) score = 0.9;
      else {
        var common = 0;
        for (var i = 0; i < q.length; i++) if (n.indexOf(q[i]) >= 0) common++;
        score = common / Math.max(q.length, n.length);
        if (Math.abs(q.length - n.length) <= 2) score = Math.max(score, 0.45);
      }
      return { name: s.name, score: score };
    }).filter(function (r) { return r.score >= 0.4; });

    scored.sort(function (a, b) { return b.score - a.score; });
    return scored.slice(0, 4).map(function (r) { return r.name; });
  }

  /* ----------------------------- 查找与展示 ----------------------------- */

  function findStudent(query) {
    var q = normName(query);
    if (!q) return null;
    for (var i = 0; i < DATA.students.length; i++) {
      var s = DATA.students[i];
      if (normName(s.name) === q) return s;
      for (var j = 0; j < s.aliases.length; j++) {
        if (normName(s.aliases[j]) === q) return s;
      }
    }
    return null;
  }

  function showResult(student, lock, scroll) {
    var result = $("#result");
    var nf = $("#notFound");

    result.innerHTML = renderReport(student, lock);
    result.hidden = false;
    nf.hidden = true;
    nf.innerHTML = "";
    $("#intro").hidden = true;
    setHint(lock
      ? "查询成功。本机已绑定「" + student.name + "」，有效期至 " + formatLockTime(lock.exp) + "；查询其他姓名无效。"
      : "查询成功，成绩如下。如需保存，可点击「打印 / 保存 PDF」。");

    countUp($("#totalValue"));

    var printBtn = $("#printBtn");
    if (printBtn) printBtn.addEventListener("click", doPrint);

    var again = $("#againBtn");
    if (again) again.addEventListener("click", function () {
      $("#nameInput").value = "";
      var pw = $("#pwInput");
      if (pw) pw.value = "";
      $("#nameInput").focus();
      result.hidden = true;
      result.innerHTML = "";
      $("#intro").hidden = false;
      setHint(authRequired ? "输入姓名和查询密码，即可查询。" : "输入与学籍一致的姓名，回车即可查询。");
      window.scrollTo({ top: 0, behavior: prefersReducedMotion() ? "auto" : "smooth" });
    });

    if (scroll !== false) smoothScrollTo(result);
  }

  /* ----------------------------- 渲染：本机已锁定 ----------------------------- */

  function renderLocked(lock, attempted) {
    return '' +
      '<div class="not-found-card" role="alert">' +
        '<span class="nf-ico nf-ico-lock" aria-hidden="true">' +
          '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round">' +
            '<rect x="4" y="10.5" width="16" height="9.5" rx="2.2"></rect>' +
            '<path d="M8 10.5V7.5a4 4 0 0 1 8 0v3"></path>' +
            '<circle cx="12" cy="15.4" r="1.3" fill="currentColor" stroke="none"></circle>' +
          '</svg>' +
        '</span>' +
        '<h2 class="nf-title">本机已查询过「' + esc(lock.name) + '」</h2>' +
        '<p class="nf-text">每台设备只能查询一位同学的成绩，查询「' + esc(attempted) + '」无效。<br>' +
          '锁定有效期至 ' + formatLockTime(lock.exp) + '，到期后自动解除。</p>' +
        '<div class="nf-chips">' +
          '<button type="button" class="chip" data-name="' + esc(lock.name) + '">查看「' + esc(lock.name) + '」的成绩</button>' +
        '</div>' +
        '<p class="nf-note">教室公用电脑或需更换查询对象时，请老师用 <code>?reset</code> 解除锁定。</p>' +
      '</div>';
  }

  function showLocked(lock, attempted) {
    var result = $("#result");
    var nf = $("#notFound");

    result.hidden = true;
    result.innerHTML = "";
    nf.innerHTML = renderLocked(lock, attempted);
    nf.hidden = false;
    $("#intro").hidden = true;
    setHint("本机已绑定「" + lock.name + "」，查询其他姓名无效。", true);

    nf.querySelectorAll(".chip").forEach(function (btn) {
      btn.addEventListener("click", function () {
        var name = btn.getAttribute("data-name");
        $("#nameInput").value = name;
        submit(name);
      });
    });

    smoothScrollTo(nf);
  }

  function showNotFound(query) {
    var result = $("#result");
    var nf = $("#notFound");

    result.hidden = true;
    result.innerHTML = "";
    nf.innerHTML = renderNotFound(query);
    nf.hidden = false;
    $("#intro").hidden = true;
    setHint("未找到该姓名，请核对后重试。", true);

    nf.querySelectorAll(".chip").forEach(function (btn) {
      btn.addEventListener("click", function () {
        var name = btn.getAttribute("data-name");
        $("#nameInput").value = name;
        submit(name);
      });
    });

    smoothScrollTo(nf);
  }

  function smoothScrollTo(el) {
    var top = el.getBoundingClientRect().top + window.pageYOffset - 24;
    window.scrollTo({ top: Math.max(0, top), behavior: prefersReducedMotion() ? "auto" : "smooth" });
  }

  function countUp(el) {
    if (!el) return;
    var target = Number(el.getAttribute("data-total"));
    if (!el.getAttribute("data-total") || isNaN(target)) { el.textContent = "—"; return; }
    if (prefersReducedMotion()) { el.textContent = fmt(target); return; }

    var start = performance.now();
    var dur = 720;

    function tick(now) {
      var p = clamp((now - start) / dur, 0, 1);
      var eased = 1 - Math.pow(1 - p, 3);
      el.textContent = fmt(Math.round(target * eased * 10) / 10);
      if (p < 1) requestAnimationFrame(tick);
      else el.textContent = fmt(target);
    }
    requestAnimationFrame(tick);
  }

  function setHint(text, isError) {
    var hint = $("#hint");
    hint.textContent = text;
    hint.classList.toggle("is-error", !!isError);
  }

  /* ----------------------------- 查询入口 ----------------------------- */

  function shakeRow(el) {
    if (!el) return;
    el.classList.remove("shake");
    void el.offsetWidth;
    el.classList.add("shake");
  }

  function submit(rawName) {
    var input = $("#nameInput");
    var pwInput = $("#pwInput");
    var query = String(rawName == null ? input.value : rawName).trim();
    hideSuggest();

    if (!query) {
      shakeRow($("#inputRow"));
      setHint("请先输入姓名，再点击查询。", true);
      input.focus();
      return;
    }

    var lock = lockMinutes > 0 ? readLock() : null;
    var student = findStudent(query);
    var lockStudent = lock ? findStudent(lock.name) : null;
    var isOwn = !!(lockStudent && student && lockStudent === student);

    if (lock && !isOwn) {
      showLocked(lock, query);
      return;
    }

    if (!student) {
      showNotFound(query);
      try { history.replaceState(null, "", location.pathname); } catch (err) { /* ignore */ }
      return;
    }

    // 首次查询（或未绑定本机）必须通过密码校验
    if (authRequired && !isOwn) {
      var pw = normalizePassword(pwInput ? pwInput.value : "");
      if (!pw) {
        shakeRow($("#pwRow"));
        setHint("请输入查询密码（" + passwordHint + "）。", true);
        if (pwInput) pwInput.focus();
        return;
      }
      if (!student.auth) {
        setHint("该同学尚未设置查询密码，请联系班主任。", true);
        return;
      }
      if (!verifyPassword(student, pw)) {
        if (pwInput) { pwInput.value = ""; pwInput.focus(); }
        shakeRow($("#pwRow"));
        setHint("密码不正确，请核对" + passwordHint + "。", true);
        return;
      }
    }

    var lockNow = null;
    if (lockMinutes > 0) {
      lockNow = readLock() || writeLock(student.name);
      applyLockedUI(lockNow);
    }
    showResult(student, lockNow);
    try {
      history.replaceState(null, "", "?name=" + encodeURIComponent(student.name));
    } catch (err) { /* file:// 等环境可能不支持，忽略 */ }
  }

  /* ----------------------------- 姓名联想 ----------------------------- */

  var activeIndex = -1;

  function hideSuggest() {
    var box = $("#suggest");
    box.hidden = true;
    box.innerHTML = "";
    activeIndex = -1;
    var input = $("#nameInput");
    if (input) input.setAttribute("aria-expanded", "false");
  }

  function renderSuggest(query) {
    var box = $("#suggest");
    var q = normName(query);

    if (!q) { hideSuggest(); return; }

    var matches = DATA.students.filter(function (s) {
      return normName(s.name).indexOf(q) >= 0;
    }).slice(0, 8);

    if (!matches.length) { hideSuggest(); return; }

    box.innerHTML = matches.map(function (s, i) {
      return '<li role="option" aria-selected="false" data-name="' + esc(s.name) + '">' +
        '<span class="s-avatar" aria-hidden="true">' + esc(s.name.slice(0, 1)) + '</span>' +
        '<span>' + highlight(s.name, query) + '</span></li>';
    }).join("");
    box.hidden = false;
    activeIndex = -1;
    $("#nameInput").setAttribute("aria-expanded", "true");

    box.querySelectorAll("li").forEach(function (li) {
      li.addEventListener("mousedown", function (e) {
        e.preventDefault();
        var name = li.getAttribute("data-name");
        $("#nameInput").value = name;
        hideSuggest();
        var pw = $("#pwInput");
        if (authRequired && pw && !pw.disabled) { pw.focus(); return; }
        submit(name);
      });
    });
  }

  function highlight(name, query) {
    var q = String(query).trim();
    if (!q) return esc(name);
    var i = name.toLowerCase().indexOf(q.toLowerCase());
    if (i < 0) return esc(name);
    return esc(name.slice(0, i)) + "<mark>" + esc(name.slice(i, i + q.length)) + "</mark>" + esc(name.slice(i + q.length));
  }

  function moveActive(step) {
    var box = $("#suggest");
    var items = Array.prototype.slice.call(box.querySelectorAll("li"));
    if (!items.length) return;
    activeIndex = (activeIndex + step + items.length) % items.length;
    items.forEach(function (li, i) {
      li.setAttribute("aria-selected", i === activeIndex ? "true" : "false");
    });
  }

  /* ----------------------------- 打印 ----------------------------- */

  function doPrint() {
    var old = document.title;
    var name = $(".student-name");
    if (name) document.title = DATA.meta.className + "成绩单 · " + name.textContent.trim();
    window.print();
    window.setTimeout(function () { document.title = old; }, 400);
  }

  /* ----------------------------- 初始化 ----------------------------- */

  function showFatal(message) {
    var box = $("#result");
    box.innerHTML = '<div class="not-found-card"><span class="nf-ico" aria-hidden="true">!</span>' +
      '<h2 class="nf-title">成绩数据尚未就绪</h2><p class="nf-text">' + esc(message) + '</p></div>';
    box.hidden = false;
    $("#intro").hidden = true;
    $("#searchForm").hidden = true;
    $("#examLine").textContent = "等待导入成绩数据";
  }

  function init() {
    var raw = window.GRADES_DATA;
    if (!raw || !Array.isArray(raw.students) || !Array.isArray(raw.subjects) || !raw.students.length) {
      showFatal("未读取到 data/grades.js 中的成绩数据，请按说明填写后再刷新页面。");
      return;
    }

    DATA = normalizeData(raw);
    INDEX = buildIndex(DATA);
    lockMinutes = DATA.meta.lockMinutes;
    passwordHint = DATA.meta.passwordHint;
    authRequired = !!(DATA.meta.requirePassword && DATA.students.some(function (s) { return !!s.auth; }));

    // 头部信息
    $("#classTag").textContent = DATA.meta.gradeName || DATA.meta.className;
    $("#examLine").textContent = DATA.meta.examName + (authRequired ? " · 姓名 + 密码查询" : " · 输入姓名即可查询");
    document.title = DATA.meta.className + "成绩发布页";
    $("#updatedLine").textContent = DATA.meta.updatedAt ? "更新时间：" + DATA.meta.updatedAt : "更新时间：—";
    $("#sampleFlag").hidden = !DATA.meta.isSample;

    var badge = $("#countBadge");
    badge.textContent = "已录入 " + DATA.students.length + " 人";
    badge.hidden = false;

    // 没配置密码时藏起密码框，退回“只输姓名”的老用法
    if (!authRequired) {
      var pwFieldHidden = $("#pwField");
      if (pwFieldHidden) pwFieldHidden.hidden = true;
      var formNoteHidden = $("#formNote");
      if (formNoteHidden) formNoteHidden.hidden = true;
    } else {
      var tipEl = $("#pwTip");
      if (tipEl) tipEl.textContent = passwordHint;
      // 6 位数字密码用数字键盘，字母密码用普通键盘
      var pwKeyboard = $("#pwInput");
      if (pwKeyboard) {
        var mode = DATA.meta.passwordInput;
        var numericPw = mode === "numeric" ||
          (mode !== "text" && /学号|数字/.test(passwordHint));
        pwKeyboard.setAttribute("inputmode", numericPw ? "numeric" : "text");
      }
    }

    var input = $("#nameInput");
    var pwInput = $("#pwInput");

    // 表单事件
    $("#searchForm").addEventListener("submit", function (e) {
      e.preventDefault();
      if (activeIndex >= 0) {
        var li = $("#suggest").querySelectorAll("li")[activeIndex];
        if (li) {
          var picked = li.getAttribute("data-name");
          input.value = picked;
          hideSuggest();
          if (authRequired && pwInput && !pwInput.disabled) pwInput.focus();
          else submit(picked);
          return;
        }
      }
      submit();
    });

    input.addEventListener("input", function () { renderSuggest(input.value); });
    input.addEventListener("focus", function () { if (input.value) renderSuggest(input.value); });
    input.addEventListener("keydown", function (e) {
      var box = $("#suggest");
      if (box.hidden) return;
      if (e.key === "ArrowDown") { e.preventDefault(); moveActive(1); }
      else if (e.key === "ArrowUp") { e.preventDefault(); moveActive(-1); }
      else if (e.key === "Escape") { hideSuggest(); }
    });

    document.addEventListener("click", function (e) {
      if (!e.target.closest(".search-card")) hideSuggest();
    });

    // 密码显示 / 隐藏（手机上避免打错）
    var pwToggle = $("#pwToggle");
    if (pwToggle) {
      pwToggle.addEventListener("click", function () {
        var show = pwInput.type === "password";
        pwInput.type = show ? "text" : "password";
        pwToggle.textContent = show ? "隐藏" : "显示";
        pwToggle.setAttribute("aria-pressed", show ? "true" : "false");
        pwToggle.setAttribute("aria-label", show ? "隐藏密码" : "显示密码");
      });
    }

    // 支持 ?name=张三 预填姓名；?reset 解除本机锁定
    var params = new URLSearchParams(location.search);
    var deepName = params.get("name");

    if (lockMinutes > 0 && params.has("reset")) {
      dropLock();
      clearLockedUI();
      try { history.replaceState(null, "", location.pathname); } catch (err) { /* ignore */ }
      setHint("已解除本机查询锁定，可以重新查询" + (authRequired ? "（需输入密码）" : "") + "。");
      input.focus();
      return;
    }

    // 本机已锁定：直接展示本人成绩，其他姓名一律无效
    if (lockMinutes > 0) {
      var lock = readLock();
      if (lock) {
        var lockedStudent = findStudent(lock.name);
        if (lockedStudent) {
          applyLockedUI(lock);
          showResult(lockedStudent, lock, false);
          return;
        }
        dropLock();
      }
    }

    if (deepName) {
      input.value = deepName;
      if (authRequired) {
        setHint("请输入查询密码（" + passwordHint + "）。");
        if (pwInput) pwInput.focus();
      } else {
        submit(deepName);
      }
    } else {
      setHint(authRequired
        ? "输入姓名和查询密码（" + passwordHint + "）后点击查询；首次查询成功会绑定本机。"
        : "输入与学籍一致的姓名，回车即可查询。每台设备只能查询一位同学。");
      // 触屏设备不自动弹出键盘，避免遮挡页面
      var canAutoFocus = window.matchMedia && window.matchMedia("(pointer: fine)").matches;
      if (canAutoFocus) {
        window.setTimeout(function () { input.focus({ preventScroll: true }); }, 260);
      }
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
