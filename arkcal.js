/*!
 * arkcal —— 用 7 9 9 3 2 5 表示任意数字
 * 规则：6 个数字必须按 7→9→9→3→2→5 的顺序出现；可拼接（79、799、799325…）；
 *      只用 + - * / 与括号。数字串可以按序重复使用。
 * 思路承自 itorr/homo（恶臭数字论证器）：先枚举「一整串能表示的数」，再贪心分解。
 */
(function (global) {
	"use strict";

	var DIGITS = [7, 9, 9, 3, 2, 5];
	var BLOCK = DIGITS.join(""); // "799325"
	var MAX_ABS = 1e15;          // 受 Number 精度限制
	var MAX_SCALE = 6;           // 小数最多 6 位

	/* ---------------- 精确有理数工具（BigInt） ---------------- */

	function gcd(a, b) {
		if (a < 0n) a = -a;
		if (b < 0n) b = -b;
		while (b) { var t = a % b; a = b; b = t; }
		return a || 1n;
	}

	/* ---------------- 1. 枚举「一整串 799325」能表示的全部值 ---------------- */

	function buildTable() {
		var n = DIGITS.length;
		var dp = [];   // dp[i][j] = Map<"分子/分母", 表达式字符串>
		var i, j, k;

		for (i = 0; i < n; i++) {
			dp[i] = [];
			var num = 0;
			for (j = i + 1; j <= n; j++) {
				num = num * 10 + DIGITS[j - 1];
				var m = new Map();
				m.set(num + "/1", String(num));
				dp[i][j] = m;
			}
		}

		function put(m, nn, dd, s) {
			if (dd < 0n) { nn = -nn; dd = -dd; }
			var g = gcd(nn, dd);
			var key = (nn / g) + "/" + (dd / g);
			var old = m.get(key);
			if (old === undefined || s.length < old.length) m.set(key, s);
		}

		for (var len = 2; len <= n; len++) {
			for (i = 0; i + len <= n; i++) {
				j = i + len;
				var cur = dp[i][j];
				for (k = i + 1; k < j; k++) {
					var A = dp[i][k], B = dp[k][j];
					A.forEach(function (sa, ka) {
						var pa = ka.split("/"), an = BigInt(pa[0]), ad = BigInt(pa[1]);
						B.forEach(function (sb, kb) {
							var pb = kb.split("/"), bn = BigInt(pb[0]), bd = BigInt(pb[1]);
							put(cur, an * bd + bn * ad, ad * bd, "(" + sa + "+" + sb + ")");
							put(cur, an * bd - bn * ad, ad * bd, "(" + sa + "-" + sb + ")");
							put(cur, an * bn, ad * bd, "(" + sa + "*" + sb + ")");
							if (bn !== 0n) put(cur, an * bd, ad * bn, "(" + sa + "/" + sb + ")");
						});
					});
				}
			}
		}

		var all = dp[0][n];
		var table = Object.create(null);   // 数字 -> 表达式
		all.forEach(function (s, key) {
			var parts = key.split("/");
			if (parts[1] === "1") table[parts[0]] = s;
		});
		return table;
	}

	/* ---------------- 2. 贪心分解 ---------------- */

	function build(api) {
		var table = buildTable();
		var values = Object.keys(table)
			.map(Number)
			.filter(function (v) { return v > 0; })
			.sort(function (a, b) { return a - b; });

		var memo = new Map();

		// 返回「可直接拼接」的串：要么是纯数字，要么整体带括号
		function demolish(num) {
			if (num === 0) return table["0"];
			var hit = memo.get(num);
			if (hit !== undefined) return hit;
			var direct = table[String(num)];
			if (direct !== undefined) { memo.set(num, direct); return direct; }

			// 找到 <= num 的最大可表示数
			var lo = 0, hi = values.length - 1, v = 0;
			while (lo <= hi) {
				var mid = (lo + hi) >> 1;
				if (values[mid] <= num) { v = values[mid]; lo = mid + 1; }
				else hi = mid - 1;
			}
			if (v < 2) throw new Error("内部错误：无法分解 " + num);

			var q = Math.floor(num / v);
			var r = num - q * v;
			var ve = table[String(v)];
			var s;
			if (r === 0) s = q === 1 ? ve : "(" + ve + "*" + demolish(q) + ")";
			else s = q === 1
				? "(" + ve + "+" + demolish(r) + ")"
				: "(" + ve + "*" + demolish(q) + "+" + demolish(r) + ")";
			memo.set(num, s);
			return s;
		}

		/* ---------------- 3. 去掉多余括号 ---------------- */

		function parse(s) {
			var i = 0;
			function expr() {
				var l = term();
				while (i < s.length && (s[i] === "+" || s[i] === "-")) {
					var op = s[i++];
					l = { t: "b", op: op, l: l, r: term() };
				}
				return l;
			}
			function term() {
				var l = factor();
				while (i < s.length && (s[i] === "*" || s[i] === "/")) {
					var op = s[i++];
					l = { t: "b", op: op, l: l, r: factor() };
				}
				return l;
			}
			function factor() {
				if (s[i] === "-") { i++; return { t: "u", e: factor() }; }
				if (s[i] === "(") { i++; var e = expr(); if (s[i] === ")") i++; return e; }
				var j = i;
				while (j < s.length && s[j] >= "0" && s[j] <= "9") j++;
				var v = s.slice(i, j);
				i = j;
				return { t: "n", v: v };
			}
			return expr();
		}

		function prec(op) { return op === "+" || op === "-" ? 1 : 2; }

		function render(node, parentPrec, isRight, parentOp) {
			if (node.t === "n") return node.v;
			if (node.t === "u") {
				var inner = render(node.e, 3, false, "");
				return "-" + inner;
			}
			var p = prec(node.op);
			var ls = render(node.l, p, false, node.op);
			var rs = render(node.r, p, true, node.op);
			var s = ls + node.op + rs;
			var need = p < parentPrec ||
				(p === parentPrec && isRight && (parentOp === "-" || parentOp === "/"));
			return need ? "(" + s + ")" : s;
		}

		function tidy(s) { return render(parse(s), 0, false, ""); }

		/* ---------------- 4. 对外接口 ---------------- */

		function toRational(input) {
			var s = String(input).trim().replace(/[\s,，_]/g, "");
			if (!s) throw new Error("先输入一个数字吧");
			var neg = false;
			if (s[0] === "-") { neg = true; s = s.slice(1); }
			else if (s[0] === "+") s = s.slice(1);
			if (!/^\d+(\.\d+)?$/.test(s)) throw new Error("看不懂「" + input + "」，只支持十进制数字");
			var frac = "";
			var dot = s.indexOf(".");
			if (dot >= 0) { frac = s.slice(dot + 1); s = s.slice(0, dot); }
			frac = frac.replace(/0+$/, "");
			if (frac.length > MAX_SCALE) throw new Error("小数最多 " + MAX_SCALE + " 位");
			if (s.length > 16) throw new Error("数字太大了，试试 1e15 以内的");
			var digits = (s + frac).replace(/^0+(?=\d)/, "");
			var big = BigInt(digits);
			if (big > BigInt(MAX_ABS)) throw new Error("数字太大了，试试 1e15 以内的");
			return { int: Number(big), scale: frac.length, neg: neg, zero: big === 0n };
		}

		function arkcal(input) {
			var r = toRational(input);
			var body;
			if (r.scale === 0) {
				body = tidy(demolish(r.int));
			} else {
				var den = Math.pow(10, r.scale);
				body = tidy("(" + demolish(r.int) + "/" + demolish(den) + ")");
			}
			if (r.neg && !r.zero) body = /^\d+$/.test(body) ? "-" + body : "-(" + body + ")";
			return body;
		}

		var maxBlock = Math.max.apply(null, values);
		arkcal.meta = {
			table: values.length + 1,   // 含 0
			max: maxBlock,
			maxBlock: maxBlock,
			block: BLOCK,
			maxAbs: MAX_ABS
		};

		return arkcal;
	}

	var api = build();
	global.arkcal = api;
	if (typeof module === "object" && module.exports) module.exports = api;

})(typeof window !== "undefined" ? window : globalThis);
