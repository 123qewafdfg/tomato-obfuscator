/**
 * fastest-obfuscation.js — 最速混淆（极速像素行置乱算法）
 * 直接从小程序 picEncryptRow.js 移植的原始混淆代码
 * 保证 100% 算法兼容性
 */
(function () {
  'use strict';

  var r = (Math.sqrt(5) - 1) / 2;

  function n(n, t, e, a, u) {
    var o = function(r, n) {
        r.sort((function(r, n) {
          return r.value > n.value ? 1 : -1
        }));
        for (var t = new Int32Array(n), e = 0; e < n; ++e) t[e] = r[e].index;
        return t
      }(function(r, n) {
        var t = new Array(n),
          e = r;
        t[0] = {
          value: e,
          index: 0
        };
        for (var a = 1; a < n; ++a) e = 3.9999999 * e * (1 - e), t[a] = {
          value: e,
          index: a
        };
        return t
      }(function(n) {
        var t = n - Math.floor(n);
        return (t <= 1e-4 || t >= .9999) && ((t = (Math.abs(n) + 1) * r % 1) <= 1e-4 || t >= .9999) && (t = r), t
      }(a), t), t),
      f = new Uint8ClampedArray(n.length),
      v = 4 * t;
    if (u)
      for (var i = 0; i < t; ++i)
        for (var l = 4 * o[i], c = 4 * i, s = 0; s < n.length; s += v) {
          var h = s + l,
            d = s + c;
          f[d] = n[h], f[d + 1] = n[h + 1], f[d + 2] = n[h + 2], f[d + 3] = n[h + 3]
        } else
          for (var y = 0; y < t; ++y)
            for (var p = 4 * y, x = 4 * o[y], g = 0; g < n.length; g += v) {
              var w = g + p,
                A = g + x;
              f[A] = n[w], f[A + 1] = n[w + 1], f[A + 2] = n[w + 2], f[A + 3] = n[w + 3]
            }
    return f
  }

  // 暴露到全局
  window.FastestObfuscation = {
    fastEncrypt: function(r, t, e, a) {
      return n(r, t, 0, a, !0)
    },
    fastDecrypt: function(r, t, e, a) {
      return n(r, t, 0, a, !1)
    },
    keyToNumber: function(keyStr) {
      if (!keyStr || keyStr === '') {
        return r;
      }
      var num = parseFloat(keyStr);
      if (!isNaN(num) && isFinite(num)) {
        return num;
      }
      // 字符串哈希
      var hash = 0;
      for (var i = 0; i < keyStr.length; i++) {
        hash = ((hash << 5) - hash) + keyStr.charCodeAt(i);
        hash |= 0;
      }
      return Math.abs(hash) || 1;
    },
    getMethodLabel: function() {
      return '最速混淆';
    }
  };
})();
