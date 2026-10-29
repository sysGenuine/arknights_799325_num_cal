#!/usr/bin/env node
/**
 * verify.js — 「799325 数字论证器」独立校验脚本（Node，无第三方依赖）
 *
 * 用法:
 *   node verify.js                    校验同目录 arkcal.js
 *   node verify.js --quick            快速冒烟（约 900 项，用于开发期）
 *   node verify.js --engine=<path>    指定引擎文件（默认 __dirname/arkcal.js）
 *   node verify.js --verbose          额外打印每个 suite 的细节
 *   node verify.js --no-progress      不打印 PASS 进度行
 *   node verify.js --selftest         只跑「校验器自检」，不加载引擎
 *
 * 退出码:
 *   0  全部通过
 *   1  有校验失败（会打印前 10 个反例）
 *   2  引擎不存在 / 加载失败 / 未定义 window.homo799325（引擎尚未完成）
 *   3  校验器内部自检失败（解析器 / 分数运算本身有 bug）
 *   64 命令行参数错误
 *
 * 实现要点（按 SPEC §三）:
 *   - 递归下降解析 + - * / 括号、前导负号、任意空白；用 BigInt 分数精确求值；全程禁用 eval / Function。
 *   - 归一化：把表达式中所有数字 token 拼起来，必须匹配 ^(799325)+$。
 *   - 每个返回值同时检查：string / 非空 / 字符集 / 精确值 / 数字串顺序。
 *   - arkcal.js 是浏览器全局脚本，这里用 vm 造一个带 window 的沙箱执行源码，不改动引擎文件。
 */

'use strict';

const fs = require('fs');
const path = require('path');
const vm = require('vm');
const crypto = require('crypto');

const SCRIPT_DIR = __dirname;
const DEFAULT_ENGINE = path.join(SCRIPT_DIR, 'arkcal.js');
const DIGITS_RE = /^(799325)+$/;
const ALLOWED_CHARS_RE = /^[0-9+\-*\/()\s]+$/;
const MAX_EXPR_LEN = 2000000; // 单条表达式长度上限（防止异常输出把校验器拖死）

/* =========================================================================
 * 1. BigInt 有理数（分子 / 分母，恒既约、分母恒正）
 * ========================================================================= */

function biAbs(x) { return x < 0n ? -x : x; }

function biGcd(a, b) {
  a = biAbs(a); b = biAbs(b);
  while (b !== 0n) { const t = a % b; a = b; b = t; }
  return a;
}

/** 构造既约分数；den 省略即整数 */
function fract(num, den) {
  let n = BigInt(num);
  let d = den === undefined ? 1n : BigInt(den);
  if (d === 0n) throw new Error('分数分母为 0');
  if (d < 0n) { n = -n; d = -d; }
  const g = biGcd(n, d);
  if (g > 1n) { n /= g; d /= g; }
  return { num: n, den: d };
}

function fAdd(a, b) { return fract(a.num * b.den + b.num * a.den, a.den * b.den); }
function fSub(a, b) { return fract(a.num * b.den - b.num * a.den, a.den * b.den); }
function fMul(a, b) { return fract(a.num * b.num, a.den * b.den); }
function fDiv(a, b) {
  if (b.num === 0n) throw new Error('表达式中出现除以零');
  return fract(a.num * b.den, a.den * b.num);
}
function fEq(a, b) { return a.num === b.num && a.den === b.den; }
function fStr(f) { return f.den === 1n ? String(f.num) : f.num + '/' + f.den; }

/* =========================================================================
 * 2. 词法 / 语法分析（递归下降，禁止 eval / Function）
 *    expr    := term (('+' | '-') term)*
 *    term    := unary (('*' | '/') unary)*
 *    unary   := ('+' | '-') unary | primary
 *    primary := NUMBER | '(' expr ')'
 *    NUMBER  := 十进制整数（不含小数点；小数点属于非法字符，由字符集检查拦下）
 * ========================================================================= */

function tokenize(text) {
  const tokens = [];
  let i = 0;
  while (i < text.length) {
    const ch = text[i];
    if (/\s/.test(ch)) { i += 1; continue; }
    if (ch >= '0' && ch <= '9') {
      let j = i;
      while (j < text.length && text[j] >= '0' && text[j] <= '9') j += 1;
      tokens.push({ type: 'num', text: text.slice(i, j), pos: i });
      i = j; continue;
    }
    if (ch === '+' || ch === '-' || ch === '*' || ch === '/') {
      tokens.push({ type: 'op', text: ch, pos: i }); i += 1; continue;
    }
    if (ch === '(') { tokens.push({ type: 'lp', text: '(', pos: i }); i += 1; continue; }
    if (ch === ')') { tokens.push({ type: 'rp', text: ')', pos: i }); i += 1; continue; }
    throw new Error('表达式含非法字符 ' + JSON.stringify(ch) + '（位置 ' + i + '）');
  }
  return tokens;
}

/**
 * 解析并求值。
 * @returns {{ value: {num: bigint, den: bigint}, numbers: string[] }}
 */
function parseExpression(text) {
  if (typeof text !== 'string') throw new Error('表达式不是字符串');
  const tokens = tokenize(text);
  if (tokens.length === 0) throw new Error('表达式为空');

  const numbers = [];
  for (const t of tokens) if (t.type === 'num') numbers.push(t.text);

  let i = 0;
  const cur = () => tokens[i];
  const isOp = (t, chars) => !!t && t.type === 'op' && chars.indexOf(t.text) >= 0;

  function parseExpr() {
    let v = parseTerm();
    while (isOp(cur(), '+-')) {
      const op = cur().text; i += 1;
      const r = parseTerm();
      v = op === '+' ? fAdd(v, r) : fSub(v, r);
    }
    return v;
  }

  function parseTerm() {
    let v = parseUnary();
    while (isOp(cur(), '*/')) {
      const op = cur().text; i += 1;
      const r = parseUnary();
      v = op === '*' ? fMul(v, r) : fDiv(v, r);
    }
    return v;
  }

  function parseUnary() {
    const t = cur();
    if (isOp(t, '+-')) {
      i += 1;
      const v = parseUnary();
      return t.text === '-' ? fract(-v.num, v.den) : v;
    }
    return parsePrimary();
  }

  function parsePrimary() {
    const t = cur();
    if (!t) throw new Error('表达式意外结束（缺少操作数）');
    if (t.type === 'num') { i += 1; return fract(BigInt(t.text)); }
    if (t.type === 'lp') {
      i += 1;
      const v = parseExpr();
      const close = cur();
      if (!close || close.type !== 'rp') throw new Error('括号不匹配（缺少 ")"）');
      i += 1;
      return v;
    }
    if (t.type === 'rp') throw new Error('括号不匹配（多余的 ")"，位置 ' + t.pos + '）');
    throw new Error('位置 ' + t.pos + ' 处出现意外运算符 ' + JSON.stringify(t.text));
  }

  const value = parseExpr();
  if (i !== tokens.length) {
    const t = tokens[i];
    throw new Error('表达式在位置 ' + t.pos + ' 处有多余内容 ' + JSON.stringify(t.text));
  }
  return { value: value, numbers: numbers };
}

/* =========================================================================
 * 3. 归一化检查：数字 token 拼接后必须匹配 ^(799325)+$
 * ========================================================================= */

function checkNormalization(numbers) {
  if (!numbers || numbers.length === 0) {
    return { ok: false, reason: '表达式中没有任何数字 token' };
  }
  for (const n of numbers) {
    if (!/^[0-9]+$/.test(n)) {
      return { ok: false, reason: '数字 token ' + JSON.stringify(n) + ' 含非数字字符（数字 token 只允许 0-9）' };
    }
  }
  const joined = numbers.join('');
  if (!DIGITS_RE.test(joined)) {
    return {
      ok: false,
      reason: '数字串顺序/片段不符：拼接后为 ' + JSON.stringify(clip(joined, 160)) +
              '（长度 ' + joined.length + '），要求匹配 ^(799325)+$'
    };
  }
  return { ok: true, joined: joined };
}

/* =========================================================================
 * 4. 输入值 -> 精确有理数（小数/科学计数法按十进制字面值转分数）
 * ========================================================================= */

const DECIMAL_RE = /^([+-]?)([0-9]*)(?:\.([0-9]*))?(?:[eE]([+-]?[0-9]+))?$/;

function fracFromDecimalString(raw) {
  const s = String(raw).trim();
  if (s === '') throw new Error('空字符串不是合法数值');
  if (/^[+-]?(Infinity|NaN)$/i.test(s)) throw new Error('非有限数值: ' + s);
  const m = DECIMAL_RE.exec(s);
  if (!m || (m[2] === '' && (m[3] === undefined || m[3] === ''))) {
    throw new Error('无法解析的十进制数值: ' + JSON.stringify(raw));
  }
  const sign = m[1] === '-' ? -1n : 1n;
  const intPart = m[2] || '';
  const fracPart = m[3] || '';
  const expRaw = m[4];
  const exp = expRaw === undefined ? 0 : Number(expRaw);
  if (!Number.isInteger(exp) || Math.abs(exp) > 400) throw new Error('指数过大: ' + s);

  let num = BigInt((intPart === '' ? '0' : intPart) + fracPart);
  let den = 10n ** BigInt(fracPart.length);
  if (exp > 0) num *= 10n ** BigInt(exp);
  else if (exp < 0) den *= 10n ** BigInt(-exp);
  return fract(sign * num, den);
}

/** 把测试输入（number 或数字字符串）转成精确分数 */
function valueToFraction(value) {
  if (typeof value === 'string') return fracFromDecimalString(value);
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) throw new Error('测试值不是有限数');
    return fracFromDecimalString(String(value)); // String(n) 是该数字最自然的十进制字面值
  }
  throw new Error('不支持的测试值类型: ' + typeof value);
}

function fmtValue(value) {
  return typeof value === 'string' ? JSON.stringify(value) : String(value);
}

function clip(s, n) {
  s = String(s);
  return s.length <= n ? s : s.slice(0, n) + '…(共 ' + s.length + ' 字符)';
}

/* =========================================================================
 * 5. 校验器自检（先证明"尺子"本身是准的）
 * ========================================================================= */

function runSelfTest() {
  const failures = [];
  let passed = 0;

  const okValue = (expr, num, den) => {
    try {
      const got = parseExpression(expr).value;
      const want = fract(BigInt(num), den === undefined ? 1n : BigInt(den));
      if (!fEq(got, want)) failures.push('求值错误 ' + JSON.stringify(expr) + '：得 ' + fStr(got) + '，期望 ' + fStr(want));
      else passed += 1;
    } catch (e) {
      failures.push('求值抛错 ' + JSON.stringify(expr) + '：' + (e && e.message));
    }
  };
  const okThrow = (expr) => {
    try { parseExpression(expr); failures.push('本应报错却解析成功: ' + JSON.stringify(expr)); }
    catch (e) { passed += 1; }
  };
  const okNorm = (nums, shouldPass) => {
    const r = checkNormalization(nums);
    if (r.ok === shouldPass) passed += 1;
    else failures.push('归一化判定错误 ' + JSON.stringify(nums) + '：期望 ' + (shouldPass ? '通过' : '失败') + '，实际 ' + (r.ok ? '通过' : '失败(' + r.reason + ')'));
  };
  const okDec = (s, num, den) => {
    try {
      const got = fracFromDecimalString(s);
      const want = fract(BigInt(num), den === undefined ? 1n : BigInt(den));
      if (!fEq(got, want)) failures.push('十进制转换错误 ' + JSON.stringify(s) + '：得 ' + fStr(got) + '，期望 ' + fStr(want));
      else passed += 1;
    } catch (e) {
      failures.push('十进制转换抛错 ' + JSON.stringify(s) + '：' + (e && e.message));
    }
  };
  const okDecThrow = (s) => {
    try { fracFromDecimalString(s); failures.push('本应拒绝的数值却接受: ' + JSON.stringify(s)); }
    catch (e) { passed += 1; }
  };

  // 解析 + 求值
  okValue('799325', '799325');
  okValue('799325+799325', '1598650');
  okValue('7+9+9+3+2+5', '35');
  okValue('-5', '-5');
  okValue('- ( 5 ) * 2', '-10');
  okValue('--5', '5');
  okValue('  1 +   2 * 3 ', '7');
  okValue('(1+2)*(3+4)', '21');
  okValue('10/4', '5', '2');
  okValue('8/2/2', '2');
  okValue('8/(2/2)', '8');
  okValue('1-2-3', '-4');
  okValue('2*(3+4)-5', '9');
  okValue('1/3+1/6', '1', '2');
  okValue('-1/2*3', '-3', '2');
  okValue('((((1))))', '1');
  okValue('-(1+2)', '-3');
  okValue('7*9*9*3*2*5', '17010');
  okValue('-7-9-9-3-2-5', '-35');
  okValue('1/7*7', '1');
  okValue('(799325-799325)', '0');

  // 语法错误必须报错，不能崩栈
  okThrow('');
  okThrow('   ');
  okThrow('(1+2');
  okThrow('1+2)');
  okThrow('1+');
  okThrow('*3');
  okThrow('/3');
  okThrow('1 2');
  okThrow('1..2');
  okThrow('abc');
  okThrow('1/0');
  okThrow('(1/0)');
  okThrow('1e5'); // 'e' 非法字符

  // 归一化判定
  okNorm(['799325'], true);
  okNorm(['799325', '799325'], true);
  okNorm(['7', '9', '9', '3', '2', '5'], true);
  okNorm(['7993255'], false);
  okNorm(['79932'], false);
  okNorm([], false);
  okNorm(['799325', '7'], false);
  okNorm(['799325', '.5'], false);
  okNorm(['0' + '799325'], false);

  // 十进制 -> 分数
  okDec('3.14', '157', '50');
  okDec('0.5', '1', '2');
  okDec('-0.25', '-1', '4');
  okDec('2.71828', '67957', '25000');
  okDec('42', '42');
  okDec('1000000000', '1000000000');
  okDec('1e3', '1000');
  okDec('-7', '-7');
  okDec('0.000001', '1', '1000000');
  okDec('.5', '1', '2');
  okDecThrow('');
  okDecThrow('abc');
  okDecThrow('NaN');
  okDecThrow('Infinity');

  return { passed: passed, failures: failures };
}

/* =========================================================================
 * 6. 加载引擎（vm + window shim，不修改 arkcal.js）
 * ========================================================================= */

function loadEngine(enginePath) {
  const result = { ok: false, fn: null, reasons: [], warnings: [], info: null };

  if (!fs.existsSync(enginePath)) {
    result.reasons.push('找不到引擎文件: ' + enginePath);
    return result;
  }
  const stat = fs.statSync(enginePath);
  const src = fs.readFileSync(enginePath, 'utf8');
  result.info = {
    path: enginePath,
    bytes: stat.size,
    mtime: stat.mtime.toISOString(),
    sha256: crypto.createHash('sha256').update(src).digest('hex').slice(0, 16)
  };

  const silent = { log: function () {}, warn: function () {}, error: function () {}, info: function () {}, debug: function () {} };

  function attempt(extra, label) {
    const sandbox = Object.assign({ console: silent, setTimeout: setTimeout, clearTimeout: clearTimeout }, extra);
    const ctx = vm.createContext(sandbox);
    // 让引擎里的 window / self 指向沙箱全局，模拟 <script> 环境
    vm.runInContext('var window = globalThis; var self = globalThis;', ctx, { filename: '<window-shim>' });
    vm.runInContext(src, ctx, { filename: path.basename(enginePath), timeout: 30000 });
    return { sandbox: sandbox, ctx: ctx };
  }

  let loaded = null;
  try {
    loaded = attempt({}, 'plain');
  } catch (e1) {
    // 引擎若在加载期碰了 document 等浏览器 API，给一个最小桩再试一次（并记录警告）
    const msg = (e1 && e1.message) ? e1.message : String(e1);
    if (/document|navigator|HTMLElement|localStorage/.test(msg)) {
      result.warnings.push('引擎在加载阶段访问了浏览器 DOM API（' + msg + '），已用最小桩重试；建议 arkcal.js 只做纯计算。');
      try {
        loaded = attempt({
          document: { addEventListener: function () {}, querySelector: function () { return null; }, getElementById: function () { return null; }, readyState: 'complete' },
          navigator: { userAgent: 'node-verify' },
          localStorage: { getItem: function () { return null; }, setItem: function () {} }
        }, 'dom-stub');
      } catch (e2) {
        result.reasons.push('执行引擎源码失败: ' + ((e2 && e2.message) ? e2.message : String(e2)));
        return result;
      }
    } else {
      result.reasons.push('执行引擎源码失败（语法错误或加载期异常）: ' + msg);
      return result;
    }
  }

  const candidates = [];
  if (loaded.sandbox.window) candidates.push(['window.homo799325', loaded.sandbox.window.homo799325]);
  candidates.push(['globalThis.homo799325', loaded.sandbox.homo799325]);

  let fn = null;
  for (const pair of candidates) {
    if (typeof pair[1] === 'function') { fn = pair[1]; break; }
  }
  if (typeof fn !== 'function') {
    result.reasons.push('引擎已执行，但没有找到函数 window.homo799325（含 globalThis.homo799325 兜底）。');
    const seen = [];
    if (loaded.sandbox.window) {
      for (const k of Object.keys(loaded.sandbox.window)) {
        if (typeof loaded.sandbox.window[k] === 'function' && k !== 'window' && k !== 'self') seen.push(k);
      }
    }
    if (seen.length) result.reasons.push('沙箱全局上可见的函数: ' + seen.join(', '));
    return result;
  }

  result.ok = true;
  result.fn = fn;
  return result;
}

/* =========================================================================
 * 7. 单个样本校验
 * ========================================================================= */

function checkOne(fn, value, expected) {
  const record = { value: value, output: '', reason: '' };

  let out;
  try {
    out = fn(value);
  } catch (e) {
    record.reason = '引擎抛错: ' + ((e && e.message) ? e.message : String(e));
    return record;
  }

  if (typeof out !== 'string') {
    record.reason = '返回值不是 string，而是 ' + (out === null ? 'null' : typeof out);
    record.output = String(out);
    return record;
  }
  record.output = out;
  if (out.trim() === '') { record.reason = '返回空字符串'; return record; }
  if (out.length > MAX_EXPR_LEN) { record.reason = '返回表达式过长（' + out.length + ' 字符 > 上限 ' + MAX_EXPR_LEN + '）'; return record; }
  if (!ALLOWED_CHARS_RE.test(out)) {
    const bad = [];
    for (const ch of out) {
      if (!/[0-9+\-*\/()\s]/.test(ch) && bad.indexOf(ch) < 0) bad.push(ch);
    }
    record.reason = '返回值含非法字符（只允许 0-9 + - * / ( ) 与空白）: ' + bad.slice(0, 8).map(function (c) { return JSON.stringify(c); }).join(', ');
    return record;
  }

  let parsed;
  try {
    parsed = parseExpression(out);
  } catch (e) {
    record.reason = '表达式解析/求值失败: ' + ((e && e.message) ? e.message : String(e));
    return record;
  }

  const norm = checkNormalization(parsed.numbers);
  if (!norm.ok) { record.reason = norm.reason; return record; }

  if (!fEq(parsed.value, expected)) {
    record.reason = '求值不符：期望 ' + fStr(expected) + '，实际 ' + fStr(parsed.value);
    return record;
  }
  return null; // 通过
}

/* =========================================================================
 * 8. 测试集
 * ========================================================================= */

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t = (t + Math.imul(t ^ (t >>> 7), t | 61)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function buildSuites(quick) {
  const suites = [];

  const intLo = quick ? -200 : -2000;
  const intHi = quick ? 200 : 2000;
  const ints = [];
  for (let n = intLo; n <= intHi; n += 1) ints.push(n);
  suites.push({ name: '全量整数 ' + intLo + '..' + intHi, values: ints });

  const stepMax = quick ? 2000 : 200000;
  const stepped = [];
  for (let n = 0; n <= stepMax; n += 7) stepped.push(n);
  suites.push({ name: '0..' + stepMax + ' 步长 7', values: stepped });

  const rnd = mulberry32(799325); // 固定种子，结果可复现
  const randoms = [];
  const randCount = quick ? 200 : 1000;
  for (let k = 0; k < randCount; k += 1) {
    randoms.push(Math.floor(rnd() * 1999999999) - 999999999); // |n| < 1e9
  }
  suites.push({ name: '随机整数 ' + randCount + ' 个（|n| < 1e9，种子 799325）', values: randoms });

  suites.push({ name: '负数专项', values: [-1, -7, -2024, -99999] });
  suites.push({ name: '小数专项', values: [3.14, 0.5, 1.5, 2.71828, -0.25] });

  // 软检查：SPEC 允许 number 或数字字符串；失败只告警、不影响退出码
  suites.push({ name: '数字字符串入参（软检查）', soft: true, values: ['42', '-42', '3.14', '0'] });

  return suites;
}

/* =========================================================================
 * 9. 边界与健壮性（软检查：只打印，不计入失败）
 *    每个输入要么返回「完全合规且值正确」的表达式，要么抛 Error；返回垃圾/错值即异常项。
 * ========================================================================= */

function runRobustness(fn) {
  const cases = [
    { label: '空串 ""', value: '' },
    { label: '纯空格 "   "', value: '   ' },
    { label: '"+7"', value: '+7' },
    { label: '"1,234"', value: '1,234' },
    { label: '"1e5"', value: '1e5' },
    { label: '"abc"', value: 'abc' },
    { label: '"NaN"', value: 'NaN' },
    { label: '"Infinity"', value: 'Infinity' },
    { label: '"0.1234567"', value: '0.1234567' },
    { label: '"1e16"', value: '1e16' }
  ];

  return cases.map(function (c) {
    const rec = { label: c.label, input: c.value, status: 'BAD', detail: '' };

    // 这个输入按契约是否应该有确定值？
    let expected = null;
    let expectedErr = null;
    try { expected = valueToFraction(c.value); } catch (e) { expectedErr = e; }

    let out;
    let threw = false;
    let errMsg = '';
    let errIsError = false;
    try {
      out = fn(c.value);
    } catch (e) {
      threw = true;
      errIsError = (e instanceof Error) || !!(e && typeof e.message === 'string');
      errMsg = (e && e.message) ? e.message : String(e);
    }

    if (threw) {
      rec.status = 'THROW';
      rec.detail = '抛出 ' + (errIsError ? 'Error' : '非 Error 值') + ': ' + JSON.stringify(clip(errMsg, 90));
      if (typeof errMsg === 'string' && !/[\u4e00-\u9fff]/.test(errMsg)) rec.detail += '  [注意: 提示里没有中文]';
      return rec;
    }

    if (expectedErr) {
      const shown = (typeof out === 'string') ? JSON.stringify(clip(out, 90)) : '类型 ' + typeof out;
      // 宽松解释：引擎可能主动剥掉分隔符（空白 / 半角逗号 / 全角逗号 / 下划线）后再解析。
      // 只要返回的表达式合规且等于剥离后的值，记为「宽松接受」，不算异常。
      let lenient = null;
      try { lenient = valueToFraction(String(c.value).trim().replace(/[\s,\uFF0C_]/g, '')); } catch (e) { lenient = null; }
      if (lenient && typeof out === 'string' && out.trim() !== '' &&
          ALLOWED_CHARS_RE.test(out) && out.length <= MAX_EXPR_LEN) {
        let parsed2 = null;
        try { parsed2 = parseExpression(out); } catch (e) { parsed2 = null; }
        if (parsed2) {
          const norm2 = checkNormalization(parsed2.numbers);
          if (norm2.ok && fEq(parsed2.value, lenient)) {
            rec.status = 'LENIENT';
            rec.detail = '宽松接受（本应拒绝，引擎剥掉了分隔符）: = ' + fStr(lenient) + '，输出 ' + shown;
            return rec;
          }
        }
      }
      rec.detail = '本应拒绝（' + expectedErr.message + '），却返回了 ' + shown;
      return rec;
    }

    if (typeof out !== 'string') { rec.detail = '返回类型 ' + typeof out + '，不是 string'; return rec; }
    if (out.trim() === '') { rec.detail = '返回空字符串'; return rec; }
    if (!ALLOWED_CHARS_RE.test(out)) { rec.detail = '返回含非法字符: ' + JSON.stringify(clip(out, 90)); return rec; }
    if (out.length > MAX_EXPR_LEN) { rec.detail = '返回表达式过长（' + out.length + ' 字符）'; return rec; }

    let parsed;
    try { parsed = parseExpression(out); } catch (e) { rec.detail = '表达式解析失败: ' + e.message; return rec; }
    const norm = checkNormalization(parsed.numbers);
    if (!norm.ok) { rec.detail = norm.reason; return rec; }
    if (!fEq(parsed.value, expected)) {
      rec.detail = '求值不符：期望 ' + fStr(expected) + '，实际 ' + fStr(parsed.value);
      return rec;
    }
    rec.status = 'OK';
    rec.detail = '= ' + fStr(expected) + '，表达式 ' + JSON.stringify(clip(out, 70));
    return rec;
  });
}

/* =========================================================================
 * 10. 主流程
 * ========================================================================= */

function parseArgs(argv) {
  const opts = { engine: DEFAULT_ENGINE, quick: false, verbose: false, progress: true, selftestOnly: false };
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i];
    if (a === '--help' || a === '-h') { opts.help = true; }
    else if (a === '--quick') opts.quick = true;
    else if (a === '--verbose' || a === '-v') opts.verbose = true;
    else if (a === '--no-progress') opts.progress = false;
    else if (a === '--selftest') opts.selftestOnly = true;
    else if (a.indexOf('--engine=') === 0) opts.engine = path.resolve(a.slice('--engine='.length));
    else { opts.error = '未知参数: ' + a; }
  }
  return opts;
}

function main() {
  const opts = parseArgs(process.argv.slice(2));

  if (opts.help) {
    console.log('用法: node verify.js [--quick] [--engine=<path>] [--verbose] [--no-progress] [--selftest]');
    console.log('退出码: 0 通过 / 1 失败 / 2 引擎缺失或加载失败 / 3 校验器自检失败 / 64 参数错误');
    process.exit(0);
  }
  if (opts.error) {
    console.error(opts.error);
    console.error('用法: node verify.js [--quick] [--engine=<path>] [--verbose] [--no-progress] [--selftest]');
    process.exit(64);
  }

  console.log('=== 799325 数字论证器 · 独立校验 ===');
  console.log('Node ' + process.version + ' / 平台 ' + process.platform);

  // --- 校验器自检（尺子先校准） ---
  const self = runSelfTest();
  if (self.failures.length > 0) {
    console.error('[自检失败] 校验器自身有 bug，共 ' + self.failures.length + ' 项：');
    for (const f of self.failures.slice(0, 20)) console.error('  - ' + f);
    console.error('校验器内部错误，退出码 3');
    process.exit(3);
  }
  console.log('自检: 解析器 / BigInt 分数 / 归一化 / 十进制转换 共 ' + self.passed + ' 项通过');
  if (opts.selftestOnly) { console.log('自检通过（--selftest）。'); process.exit(0); }

  // --- 加载引擎 ---
  const engine = loadEngine(opts.engine);
  if (engine.info) {
    console.log('引擎: ' + engine.info.path);
    console.log('       ' + engine.info.bytes + ' 字节, mtime ' + engine.info.mtime + ', sha256 ' + engine.info.sha256 + '…');
  }
  for (const w of engine.warnings) console.log('[提示] ' + w);
  if (!engine.ok) {
    console.error('');
    console.error('!! 引擎尚未就绪，无法校验（退出码 2）!!');
    for (const r of engine.reasons) console.error('   - ' + r);
    console.error('   请确认 D:\\dsh\\sessions\\799325\\arkcal.js 已写好并定义 window.homo799325(value)。');
    process.exit(2);
  }
  const fn = engine.fn;

  // --- 组装测试集 ---
  const suites = buildSuites(opts.quick);
  let total = 0;
  for (const s of suites) total += s.values.length;
  console.log('测试规模: ' + total + ' 项' + (opts.quick ? '（--quick 快速模式）' : ''));
  if (opts.progress) console.log('');

  let checked = 0;
  let passed = 0;
  let failed = 0;
  let warned = 0;
  const hardFailures = [];
  const softFailures = [];
  const suiteStats = [];

  for (const suite of suites) {
    let sPass = 0;
    let sFail = 0;
    for (const value of suite.values) {
      checked += 1;
      let expected;
      try {
        expected = valueToFraction(value);
      } catch (e) {
        console.error('内部错误：无法把测试值 ' + fmtValue(value) + ' 转成分数: ' + e.message);
        process.exit(3);
      }

      let record = null;
      try {
        record = checkOne(fn, value, expected);
      } catch (e) {
        record = { value: value, output: '', reason: '校验过程异常: ' + ((e && e.message) ? e.message : String(e)) };
      }

      if (!record) { sPass += 1; passed += 1; }
      else if (suite.soft) {
        sFail += 1; warned += 1;
        if (softFailures.length < 10) softFailures.push({ suite: suite.name, record: record });
      } else {
        sFail += 1; failed += 1;
        if (hardFailures.length < 10) hardFailures.push({ suite: suite.name, record: record });
      }

      if (opts.progress && checked % 2000 === 0) {
        console.log('PASS ' + passed + ' / ' + checked + ' ...');
      }
    }
    suiteStats.push({ name: suite.name, total: suite.values.length, pass: sPass, fail: sFail, soft: !!suite.soft });
    if (opts.verbose || sFail > 0) {
      console.log('[suite] ' + suite.name + '：' + sPass + '/' + suite.values.length + ' 通过' + (sFail ? '，' + sFail + ' 失败' : ''));
    }
  }

  // --- 软检查：meta / 非法入参 ---
  const notes = [];
  try {
    const meta = fn.meta;
    if (!meta || typeof meta !== 'object') notes.push('homo799325.meta 不存在（SPEC 要求 { table, max }）');
    else {
      if (typeof meta.table !== 'number') notes.push('meta.table 不是 number');
      if (typeof meta.max !== 'number') notes.push('meta.max 不是 number');
    }
  } catch (e) {
    notes.push('读取 homo799325.meta 抛错: ' + e.message);
  }
  const badInputs = [[NaN, 'NaN'], [Infinity, 'Infinity'], ['', '空字符串'], ['abc', '非数字字符串']];
  for (const pair of badInputs) {
    let threw = false;
    let msg = '';
    try { fn(pair[0]); } catch (e) { threw = true; msg = (e && e.message) ? e.message : String(e); }
    if (!threw) notes.push('非法输入 ' + pair[1] + ' 本应 throw，实际没有抛错');
    else if (typeof msg !== 'string' || msg.trim() === '') notes.push('非法输入 ' + pair[1] + ' 抛出的错误没有可读 message');
  }

  // --- 边界与健壮性（软检查，只打印） ---
  const robustness = runRobustness(fn);

  // --- 反例输出 ---
  if (hardFailures.length > 0) {
    console.log('');
    console.log('===== 反例（前 ' + hardFailures.length + ' 个，共 ' + failed + ' 个失败）=====');
    hardFailures.forEach(function (f, idx) {
      console.log('');
      console.log('#' + (idx + 1) + ' [suite: ' + f.suite + '] 输入 = ' + fmtValue(f.record.value));
      console.log('  失败原因: ' + f.record.reason);
      console.log('  引擎输出: ' + (f.record.output === '' ? '(空)' : JSON.stringify(clip(f.record.output, 300))));
    });
  }
  if (softFailures.length > 0) {
    console.log('');
    console.log('----- 软检查失败（前 ' + softFailures.length + ' 个，仅供参考，不影响退出码）-----');
    softFailures.forEach(function (f, idx) {
      console.log('  #' + (idx + 1) + ' [suite: ' + f.suite + '] 输入 = ' + fmtValue(f.record.value));
      console.log('      原因: ' + f.record.reason);
      console.log('      输出: ' + (f.record.output === '' ? '(空)' : JSON.stringify(clip(f.record.output, 200))));
    });
  }
  if (notes.length > 0) {
    console.log('');
    console.log('----- 附注（软检查，仅供参考）-----');
    for (const n of notes) console.log('  · ' + n);
  }

  // --- 边界与健壮性明细 ---
  let robOk = 0;
  let robThrow = 0;
  let robLenient = 0;
  let robBad = 0;
  console.log('');
  console.log('----- 边界与健壮性（软检查，不影响退出码；要么正确结果、要么抛中文 Error）-----');
  for (const r of robustness) {
    if (r.status === 'OK') robOk += 1;
    else if (r.status === 'THROW') robThrow += 1;
    else if (r.status === 'LENIENT') robLenient += 1;
    else robBad += 1;
    const tag = r.status === 'OK' ? 'OK   '
      : r.status === 'THROW' ? 'THROW'
      : r.status === 'LENIENT' ? 'LEN  '
      : 'BAD  ';
    console.log('  · ' + r.label.padEnd(16) + ' → ' + tag + '  ' + r.detail);
  }
  console.log('  边界小计: 正确输出 ' + robOk + ' / 抛错 ' + robThrow + ' / 宽松接受 ' + robLenient + ' / 异常 ' + robBad +
    (robBad > 0 ? '（异常项见上，属于软检查，未计入失败）' : ''));

  // --- 汇总 ---
  console.log('');
  console.log('===== 汇总 =====');
  for (const s of suiteStats) {
    console.log((s.fail === 0 ? '  OK   ' : '  FAIL ') + s.name + '：' + s.pass + '/' + s.total + (s.soft && s.fail ? '（软检查 ' + s.fail + ' 项未过）' : ''));
  }
  if (warned > 0) console.log('  警告 ' + warned + ' 项（软检查，不计入失败）');
  console.log('PASS ' + passed + ' / ' + checked);
  console.log('通过 ' + passed + '，失败 ' + failed);

  process.exit(failed > 0 ? 1 : 0);
}

main();
