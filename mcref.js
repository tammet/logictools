// mcref.js: a JavaScript port of mcref 1.1.1, the Monte Carlo reference tool
// for the support semantics of gk's recursive method.
//
// The semantics is Doc/support_semantics.md of the gk repository. The Python
// tool is published in https://github.com/tammet/gkreasoner. This file ports
// two Python files of mcref 1.1.1:
//
//   mcref.py       sha256 c02276ac35c89ac17fe26984a4c12d79fad1ae22b49e83aea0b690c7e4598d9d
//   mcref_read.py  sha256 36063563420653033406346a5ddb129e5440c61a337e3e97c027e6f7960c60a8
//
// The functions keep the Python names in camelCase, and each block names the
// Python function it ports. For the same seed and sample count, the port
// computes the same counts as mcref.py: it draws the same splitmix64 numbers,
// visits the atoms in the same order and multiplies the same floating-point
// numbers in the same order.
//
// The port reads JSON-LD-LOGIC text only. mcref.py converts other input
// languages with `gk FILE -writejson -recursive`. A caller of this port runs
// that conversion first (the page runs the gk wasm build) and passes the
// output with the option convertedBy. The port then reads the output exactly
// as mcref.py reads it.
//
// Use in a Web Worker: post {cmd: "run", input, samples, seed, maxGround,
// allAtoms}. The worker posts {progress: n} messages while it samples, and
// then {done: true, result} or {error}. The result is the object that
// mcref.py prints under "mcref".
//
// Use under node: const {mcref} = require("./mcref.js");
// const result = mcref(text, {samples: 100000, seed: 1});
//
// Options of mcref(text, options):
//   samples      the number of worlds (default 100000)
//   seed         the seed of splitmix64 (default 1)
//   maxGround    the grounding limit (default 200000)
//   allAtoms     true: evaluate every atom and report atom_values
//   name         the text of the result's "input" field (default null)
//   convertedBy  set when the text is gk's -writejson output, for example
//                "gk -writejson -recursive"; mcref.py reads such output
//                without removing comments
//   conversionOutput  gk's full output (stdout and stderr) of the
//                conversion, for the message of a failed conversion
//   include      a function (name) -> null, a JSON-LD-LOGIC text, or
//                {text, convertedBy, conversionOutput}; it reads the file
//                of an @include statement. Without it, an @include
//                statement gives "include not found".
//   progress     a function (n) called with the number of finished worlds

(function (root) {
  "use strict";

  const VERSION = "1.1.1-js";
  const TOOL = {
    "mcref.py": "c02276ac35c89ac17fe26984a4c12d79fad1ae22b49e83aea0b690c7e4598d9d",
    "mcref_read.py": "36063563420653033406346a5ddb129e5440c61a337e3e97c027e6f7960c60a8"
  };
  const POS = 0, NEG = 1, CON = 2, IGN = 3, UNRES = 4;
  const TWO53 = Math.pow(2, -53);
  const SWEEP_CAP = 100000;
  const INTERPRETATION = {
    "semantics": "Doc/support_semantics.md, the support semantics of 2026-11-03",
    "written-head rules": "a certain rule without exception literals is used in every direction (memo 4.1); " +
      "below confidence 1 or with an exception literal, at its written head only",
    "flat clauses": "one application per literal; one source event per uncertain ground clause",
    "not represented": "a classical consequence that needs several input clauses at once",
    "domain": "the constants of the input",
    "kind of a side": "decided in each world from the applications present in it (memo 4.4, 4.5)",
    "cycles": "a cycle across signs by the narrowing of memo 5.5, ordinary applications first when the group has " +
      "normal defaults; a one-sign or exception-only group by sweeps, the narrowing only when the sweeps " +
      "repeat a state, an undecided atom then read as ignorance (memo 5.1, 5.4)",
    "unresolved": "an atom of a cycle across signs left possible but not sure (memo 5.4, 5.5); a group that depends " +
      "on an unresolved atom runs the narrowing with that atom's two literals possible and neither sure " +
      "(memo 5), and an atom of it left possible but not sure is unresolved too",
    "rank contexts (decision 13)": "not covered; an input where they can matter is unsupported",
    "self exception (decision 68)": "an application whose exception is its own body literal never applies"
  };

  const CONNECTIVES = new Set(["&", "|", "=>", "<=", "<=>", "and", "or", "not", "~", "forall", "exists", "xor",
    "nor", "nand", "<~>", "if", "then", "-"]);
  const ORDINARY_DOLLAR = new Set(["$arc", "$narc"]);

  // Unsupported is the exception of mcref_read.py: the input is outside the
  // tool's fragment, and the result names the reason.
  class Unsupported extends Error {}
  function unsup(msg) { return new Unsupported(msg); }

  // ---------------------------------------------------------------- Python values and texts
  //
  // Python's json module keeps 1 and 1.0 apart, and mcref uses the
  // difference: 1, 1.0 and "1" are three constants. The JSON reader below
  // gives an integer as a PInt and a real as a JS number.

  class PInt {
    constructor(text) {
      const b = BigInt(text);
      this.s = b.toString();   // Python's str() of the integer
      this.n = Number(b);
    }
  }

  function hexN(c, w) {
    let h = c.toString(16);
    while (h.length < w) h = "0" + h;
    return h;
  }

  // Python's repr() of a float: the shortest digits that read back as the
  // same number, in fixed notation for exponents -4 to 15, else as d.dde+XX.
  function floatRepr(x) {
    if (x !== x) return "nan";
    if (x === Infinity) return "inf";
    if (x === -Infinity) return "-inf";
    if (x === 0) return 1 / x < 0 ? "-0.0" : "0.0";
    let s = String(x), sign = "";
    if (s[0] === "-") { sign = "-"; s = s.slice(1); }
    const m = /^(\d+)(?:\.(\d+))?(?:e([+-]\d+))?$/.exec(s);
    let digits = m[1] + (m[2] || "");
    let point = m[1].length + (m[3] ? parseInt(m[3], 10) : 0);
    let z = 0;
    while (z < digits.length - 1 && digits[z] === "0") z++;
    digits = digits.slice(z);
    point -= z;
    digits = digits.replace(/0+$/, "");
    const exp = point - 1;
    if (exp >= -4 && exp < 16) {
      if (point <= 0) return sign + "0." + "0".repeat(-point) + digits;
      if (digits.length <= point) return sign + digits + "0".repeat(point - digits.length) + ".0";
      return sign + digits.slice(0, point) + "." + digits.slice(point);
    }
    const mant = digits.length > 1 ? digits[0] + "." + digits.slice(1) : digits;
    const ae = Math.abs(exp);
    return sign + mant + "e" + (exp < 0 ? "-" : "+") + (ae < 10 ? "0" + ae : String(ae));
  }

  // The characters that Python's str.isprintable() rejects outside ASCII.
  let NONPRINT;
  try {
    NONPRINT = new RegExp("^[\\p{Cc}\\p{Cf}\\p{Cs}\\p{Co}\\p{Cn}\\p{Zl}\\p{Zp}\\p{Zs}]$", "u");
  } catch (e) {
    NONPRINT = /^[\u0080- ­]$/;
  }

  // Python's repr() of a str.
  function pyStrRepr(s) {
    const q = (s.indexOf("'") >= 0 && s.indexOf('"') < 0) ? '"' : "'";
    let out = q;
    for (const ch of s) {
      const cp = ch.codePointAt(0);
      if (ch === q || ch === "\\") out += "\\" + ch;
      else if (ch === "\t") out += "\\t";
      else if (ch === "\n") out += "\\n";
      else if (ch === "\r") out += "\\r";
      else if (cp < 0x20 || cp === 0x7f) out += "\\x" + hexN(cp, 2);
      else if (cp < 0x7f) out += ch;
      else if (NONPRINT.test(ch)) {
        out += cp <= 0xff ? "\\x" + hexN(cp, 2) : (cp <= 0xffff ? "\\u" + hexN(cp, 4) : "\\U" + hexN(cp, 8));
      } else out += ch;
    }
    return out + q;
  }

  // Python's repr() of a value read from JSON.
  function pyRepr(v) {
    if (v === null || v === undefined) return "None";
    if (v === true) return "True";
    if (v === false) return "False";
    if (v instanceof PInt) return v.s;
    if (typeof v === "number") return floatRepr(v);
    if (typeof v === "string") return pyStrRepr(v);
    if (Array.isArray(v)) return "[" + v.map(pyRepr).join(", ") + "]";
    if (v instanceof Map) {
      const parts = [];
      for (const [k, x] of v) parts.push(pyStrRepr(k) + ": " + pyRepr(x));
      return "{" + parts.join(", ") + "}";
    }
    return String(v);
  }

  // Python's str() of a value read from JSON.
  function pyStr(v) {
    return typeof v === "string" ? v : pyRepr(v);
  }

  // Python's json.dumps() of a str, with ensure_ascii.
  function jsonStr(s) {
    let out = '"';
    for (let i = 0; i < s.length; i++) {
      const c = s.charCodeAt(i);
      if (c === 0x22) out += '\\"';
      else if (c === 0x5c) out += "\\\\";
      else if (c === 0x0a) out += "\\n";
      else if (c === 0x0d) out += "\\r";
      else if (c === 0x09) out += "\\t";
      else if (c === 0x08) out += "\\b";
      else if (c === 0x0c) out += "\\f";
      else if (c < 0x20 || c > 0x7e) out += "\\u" + hexN(c, 4);
      else out += s[i];
    }
    return out + '"';
  }

  // Python's json.dumps() of a value read from JSON.
  function pyJsonDumps(v) {
    if (v === null || v === undefined) return "null";
    if (v === true) return "true";
    if (v === false) return "false";
    if (v instanceof PInt) return v.s;
    if (typeof v === "number") {
      if (v !== v) return "NaN";
      if (v === Infinity) return "Infinity";
      if (v === -Infinity) return "-Infinity";
      return floatRepr(v);
    }
    if (typeof v === "string") return jsonStr(v);
    if (Array.isArray(v)) return "[" + v.map(pyJsonDumps).join(", ") + "]";
    if (v instanceof Map) {
      const parts = [];
      for (const [k, x] of v) parts.push(jsonStr(k) + ": " + pyJsonDumps(x));
      return "{" + parts.join(", ") + "}";
    }
    return String(v);
  }

  // The whitespace of Python's str.strip() and float().
  const PYWS = "[\\t\\n\\x0b\\x0c\\r\\x1c-\\x1f \\x85\\xa0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000]";
  const PYSTRIP = new RegExp("^" + PYWS + "+|" + PYWS + "+$", "g");
  function pyStrip(s) { return s.replace(PYSTRIP, ""); }

  // The strings that Python's float() accepts.
  const PYFLOAT = (function () {
    const D = "\\p{Nd}", DP = D + "(?:_?" + D + ")*";
    const num = "(?:" + DP + "(?:\\.(?:" + DP + ")?)?|\\." + DP + ")(?:[eE][+-]?" + DP + ")?";
    return new RegExp("^" + PYWS + "*[+-]?(?:" + num + "|inf|infinity|nan)" + PYWS + "*$", "iu");
  })();

  // A prefix of n code points (Python's s[:n]).
  function cpSlice(s, n) {
    if (s.length <= n) return s;
    return Array.from(s).slice(0, n).join("");
  }

  function cpLen(s) {
    let n = 0;
    for (let i = 0; i < s.length; i++) {
      const c = s.charCodeAt(i);
      if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
        const d = s.charCodeAt(i + 1);
        if (d >= 0xdc00 && d <= 0xdfff) i++;
      }
      n++;
    }
    return n;
  }

  // Python compares strings by code point; JS compares UTF-16 units. The
  // two orders differ only where a surrogate meets a unit of U+E000..U+FFFF.
  function fixUnit(u) { return u >= 0xe000 ? u - 0x800 : (u >= 0xd800 ? u + 0x2000 : u); }
  function cmpStr(a, b) {
    if (a === b) return 0;
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) {
      const x = a.charCodeAt(i), y = b.charCodeAt(i);
      if (x !== y) {
        if (x >= 0xd800 && y >= 0xd800) return fixUnit(x) < fixUnit(y) ? -1 : 1;
        return x < y ? -1 : 1;
      }
    }
    return a.length < b.length ? -1 : (a.length > b.length ? 1 : 0);
  }

  // ---------------------------------------------------------------- JSON as Python's json.loads reads it
  //
  // The reader follows the C scanner of Python 3.14's json module: the same
  // accepted texts (NaN, Infinity, -Infinity included), integers kept apart
  // from reals, objects as Maps in the order of their keys, and the same
  // error messages with line, column and character position.

  class JsonError extends Error {}

  function jsonLoads(s) {
    const n = s.length;
    let pos = 0;
    function err(msg, at) {
      const pre = s.slice(0, at);
      let lineno = 1;
      for (let i = 0; i < pre.length; i++) if (pre.charCodeAt(i) === 10) lineno++;
      const cpos = cpLen(pre);
      const colno = lineno === 1 ? cpos + 1 : cpos - cpLen(pre.slice(0, pre.lastIndexOf("\n")));
      return new JsonError(msg + ": line " + lineno + " column " + colno + " (char " + cpos + ")");
    }
    function ws(i) {
      while (i < n) {
        const c = s.charCodeAt(i);
        if (c === 32 || c === 9 || c === 10 || c === 13) i++;
        else break;
      }
      return i;
    }
    const NUM = /(-?(?:0|[1-9]\d*))(\.\d+)?([eE][-+]?\d+)?/y;
    const ESC = {'"': '"', "\\": "\\", "/": "/", "b": "\b", "f": "\f", "n": "\n", "r": "\r", "t": "\t"};
    function str(i) {
      const begin = i - 1;
      let out = "", start = i;
      while (true) {
        if (i >= n) throw err("Unterminated string starting at", begin);
        const c = s.charCodeAt(i);
        if (c === 0x22) {
          out += s.slice(start, i);
          pos = i + 1;
          return out;
        }
        if (c === 0x5c) {
          out += s.slice(start, i);
          i++;
          if (i >= n) throw err("Unterminated string starting at", begin);
          const e = s[i];
          if (e !== "u") {
            const m = ESC[e];
            if (m === undefined) throw err("Invalid \\escape", i - 1);
            out += m;
            i++;
          } else {
            i++;
            const h = s.substr(i, 4);
            if (!/^[0-9a-fA-F]{4}$/.test(h)) throw err("Invalid \\uXXXX escape", i - 1);
            out += String.fromCharCode(parseInt(h, 16));
            i += 4;
          }
          start = i;
          continue;
        }
        if (c < 0x20) throw err("Invalid control character at", i);
        i++;
      }
    }
    function arr(i) {
      const a = [];
      i = ws(i);
      if (i < n && s[i] === "]") { pos = i + 1; return a; }
      while (true) {
        a.push(value(i));
        i = ws(pos);
        if (i < n && s[i] === "]") { pos = i + 1; return a; }
        if (i >= n || s[i] !== ",") throw err("Expecting ',' delimiter", i);
        const comma = i;
        i = ws(i + 1);
        if (i < n && s[i] === "]") throw err("Illegal trailing comma before end of array", comma);
      }
    }
    function obj(i) {
      const o = new Map();
      i = ws(i);
      if (i < n && s[i] === "}") { pos = i + 1; return o; }
      if (i >= n || s[i] !== '"') throw err("Expecting property name enclosed in double quotes", i);
      while (true) {
        const key = str(i + 1);
        i = ws(pos);
        if (i >= n || s[i] !== ":") throw err("Expecting ':' delimiter", i);
        i = ws(i + 1);
        o.set(key, value(i));
        i = ws(pos);
        if (i < n && s[i] === "}") { pos = i + 1; return o; }
        if (i >= n || s[i] !== ",") throw err("Expecting ',' delimiter", i);
        const comma = i;
        i = ws(i + 1);
        if (i < n && s[i] === "}") throw err("Illegal trailing comma before end of object", comma);
        if (i >= n || s[i] !== '"') throw err("Expecting property name enclosed in double quotes", i);
      }
    }
    function value(i) {
      if (i >= n) throw err("Expecting value", i);
      const c = s[i];
      if (c === '"') return str(i + 1);
      if (c === "{") return obj(i + 1);
      if (c === "[") return arr(i + 1);
      if (c === "n" && s.startsWith("null", i)) { pos = i + 4; return null; }
      if (c === "t" && s.startsWith("true", i)) { pos = i + 4; return true; }
      if (c === "f" && s.startsWith("false", i)) { pos = i + 5; return false; }
      if (c === "N" && s.startsWith("NaN", i)) { pos = i + 3; return NaN; }
      if (c === "I" && s.startsWith("Infinity", i)) { pos = i + 8; return Infinity; }
      if (c === "-" && s.startsWith("-Infinity", i)) { pos = i + 9; return -Infinity; }
      NUM.lastIndex = i;
      const m = NUM.exec(s);
      if (!m) throw err("Expecting value", i);
      pos = i + m[0].length;
      if (m[2] || m[3]) return Number(m[0]);
      return new PInt(m[1]);
    }
    if (n > 0 && s.charCodeAt(0) === 0xfeff) throw err("Unexpected UTF-8 BOM (decode using utf-8-sig)", 0);
    const v = value(ws(0));
    const end = ws(pos);
    if (end !== n) throw err("Extra data", end);
    return v;
  }

  // ---------------------------------------------------------------- reading (mcref_read.py)

  // strip_comments: C-style comments outside JSON strings.
  function stripComments(text) {
    const out = [];
    let i = 0, instr = false;
    const n = text.length;
    while (i < n) {
      const c = text[i];
      if (instr) {
        out.push(c);
        if (c === "\\" && i + 1 < n) { out.push(text[i + 1]); i += 2; continue; }
        if (c === '"') instr = false;
        i++;
      } else if (c === '"') {
        instr = true; out.push(c); i++;
      } else if (c === "/" && i + 1 < n && text[i + 1] === "/") {
        while (i < n && text[i] !== "\n") i++;
      } else if (c === "/" && i + 1 < n && text[i + 1] === "*") {
        const j = text.indexOf("*/", i + 2);
        i = j < 0 ? n : j + 2;
      } else {
        out.push(c); i++;
      }
    }
    return out.join("");
  }

  // Python reads files and gk's output with universal newlines.
  function newlines(t) { return t.indexOf("\r") >= 0 ? t.replace(/\r\n?/g, "\n") : t; }

  // read_statements: the statement list of a text. A text with convertedBy
  // is gk's -writejson output; mcref.py reads it from the first "[" on and
  // removes no comments.
  function readStatements(text, src, conv, files, opts, depth) {
    let data;
    text = newlines(text);
    if (src.convertedBy) {
      conv.push(src.convertedBy);
      const t = pyStrip(text);
      data = null;
      const k = t.indexOf("[");
      if (k >= 0) {
        try { data = jsonLoads(t.slice(k)); } catch (e) {
          if (!(e instanceof JsonError)) throw e;
          data = null;
        }
      }
      if (data === null) {
        const log = src.conversionOutput !== undefined && src.conversionOutput !== null ?
          newlines(src.conversionOutput) : text;
        throw unsup("conversion failed: " + cpSlice(pyStrip(log), 100));
      }
    } else {
      try { data = jsonLoads(stripComments(text)); } catch (e) {
        if (!(e instanceof JsonError)) throw e;
        throw unsup("not JSON: " + cpSlice(e.message, 80));
      }
    }
    if (!Array.isArray(data)) throw unsup("the input is not a list of statements");
    const out = [];
    for (const item of data) {
      if (item instanceof Map && item.has("@include") && !item.has("@logic")) {
        const inc = item.get("@include");
        let r = typeof opts.include === "function" && depth < 50 ? opts.include(inc) : null;
        if (r === null || r === undefined) throw unsup("include not found: " + pyStr(inc));
        if (typeof r === "string") r = {text: r};
        files.push(["include " + pyStr(inc), sha256(r.text)]);
        for (const x of readStatements(r.text, r, conv, files, opts, depth + 1)) out.push(x);
      } else out.push(item);
    }
    return out;
  }

  function isVar(t) { return typeof t === "string" && t.startsWith("?:"); }

  // ---------------------------------------------------------------- constants and atoms
  //
  // A constant is a typed value, as in mcref_read.py: ("s", string),
  // ("i", integer) or ("r", real). The port keeps one object per constant
  // and per ground atom, so that equal values are the same object. An atom
  // has the fields pred, args (null for a bare string atom, else an array of
  // constants) and text (atom_text).

  let constTable = null, atomTable = null, atomList = null;

  function resetTables() {
    constTable = new Map();
    atomTable = new Map();
    atomList = [];
  }

  const SEPARATORS = /[,()"\\ \t\n]/;

  // typed and term_text
  function typed(v) {
    let key;
    if (typeof v === "string") key = "s" + v;
    else if (v instanceof PInt) key = "i" + v.s;
    else key = "r" + (v === 0 ? "0.0" : floatRepr(v));   // Python: 0.0 == -0.0
    let c = constTable.get(key);
    if (c) return c;
    c = {id: constTable.size, tag: null, text: null, str: null, num: NaN, out: null};
    if (typeof v === "string") {
      c.tag = "s"; c.str = v; c.out = v;
      c.text = (PYFLOAT.test(v) || !v || SEPARATORS.test(v)) ? jsonStr(v) : v;
    } else if (v instanceof PInt) {
      c.tag = "i"; c.str = v.s; c.text = v.s; c.num = v.n; c.out = v.n;
    } else {
      c.tag = "r"; c.str = floatRepr(v); c.text = c.str; c.num = v; c.out = v;
    }
    constTable.set(key, c);
    return c;
  }

  function termText(t) { return typeof t === "string" ? t : t.text; }

  // atom_text, for atoms with or without variables
  function atomText(pred, args) {
    if (!args || !args.length) return pred;
    return pred + "(" + args.map(termText).join(",") + ")";
  }

  function litText(sign, pred, args) { return (sign ? "-" : "") + atomText(pred, args); }

  function atomKey(pred, args) {
    if (args === null) return "N" + pred;
    let k = "A";
    for (let i = 0; i < args.length; i++) k += (i ? "," : "") + args[i].id;
    return k + "|" + pred;
  }

  // the atom object of a ground atom, made once
  function atomOf(pred, args) {
    const key = atomKey(pred, args);
    let a = atomTable.get(key);
    if (a) return a;
    a = {id: atomList.length, pred: pred, args: args, none: args === null, text: atomText(pred, args)};
    atomTable.set(key, a);
    atomList.push(a);
    return a;
  }

  function findAtom(pred, args) { return atomTable.get(atomKey(pred, args)) || null; }

  // A ground literal is the number 2 * atom id + sign.
  function codeText(c) { return (c & 1 ? "-" : "") + atomList[c >> 1].text; }

  // ---------------------------------------------------------------- formulas (mcref_read.py)
  //
  // AST nodes: {t: "lit", sign, pred, args}, {t: "block", st, lit},
  // {t: "and", parts}, {t: "or", parts}, {t: "not", a}, {t: "imp", a, b},
  // {t: "iff", a, b}, {t: "forall", a}.

  // lit_of
  function litOf(x) {
    if (typeof x === "string") {
      if (CONNECTIVES.has(x)) return null;
      if (x.startsWith("-") && x.length > 1) return {t: "lit", sign: 1, pred: x.slice(1), args: null};
      return {t: "lit", sign: 0, pred: x, args: null};
    }
    if (Array.isArray(x) && x.length && typeof x[0] === "string" && !CONNECTIVES.has(x[0]) && x[0] !== "$block") {
      for (let i = 1; i < x.length; i++) {
        if (x[i] === "=" || x[i] === "!=") throw unsup("equality");
      }
      let pred = x[0], sign = 0;
      if (pred.startsWith("-") && pred.length > 1) { sign = 1; pred = pred.slice(1); }
      if (pred === "=" || pred === "!=" || pred === "$not") {
        throw unsup(pred !== "$not" ? "equality" : "unsupported formula form: $not outside $block");
      }
      for (let i = 1; i < x.length; i++) {
        const a = x[i];
        if (Array.isArray(a) || a instanceof Map) throw unsup("function symbols");
        if (typeof a === "boolean" || a === null) throw unsup("unsupported term: " + pyRepr(a));
      }
      const args = [];
      for (let i = 1; i < x.length; i++) args.push(isVar(x[i]) ? x[i] : typed(x[i]));
      return {t: "lit", sign: sign, pred: pred, args: args};
    }
    return null;
  }

  // block_of
  function blockOf(x) {
    if (Array.isArray(x) && x.length && x[0] === "$block") {
      if (x.length !== 3) throw unsup("unsupported formula form: $block arity");
      const s = x[1], target = x[2];
      if (Array.isArray(s)) throw unsup("taxonomy strength");
      if (!(s instanceof PInt)) throw unsup("unsupported $block strength " + pyRepr(s));
      if (Array.isArray(target) && target.length && target[0] === "$not") {
        if (target.length < 2) throw new Error("mcref.py raises IndexError on a $not without an argument");
        const l = litOf(target[1]);
        if (!l) throw unsup("unsupported formula form: $block target");
        return {t: "block", st: s.n, lit: negLit(l)};
      }
      const l = litOf(target);
      if (!l) throw unsup("unsupported formula form: $block target");
      return {t: "block", st: s.n, lit: l};
    }
    return null;
  }

  // bind_forall
  function bindForall(x) {
    const names = Array.isArray(x[1]) ? x[1] : [x[1]];
    const ren = new Map();
    for (const nm of names) if (typeof nm === "string" && !nm.startsWith("?:")) ren.set(nm, "?:" + nm);
    if (!ren.size) return x[2];
    function sub(t) {
      if (Array.isArray(t)) {
        if (t.length && typeof t[0] === "string") return [t[0]].concat(t.slice(1).map(sub));
        return t.map(sub);
      }
      if (typeof t === "string") return ren.has(t) ? ren.get(t) : t;
      return t;
    }
    return sub(x[2]);
  }

  // parse
  function parse(x) {
    const l = litOf(x);
    if (l) return l;
    const b = blockOf(x);
    if (b) return b;
    if (!Array.isArray(x) || !x.length) throw unsup("unsupported formula form: " + pyRepr(x));
    const h = x[0];
    if (typeof h === "string" && (h === "not" || h === "~" || h === "-") && x.length === 2) {
      return {t: "not", a: parse(x[1])};
    }
    if (h === "forall" && x.length === 3) return {t: "forall", a: parse(bindForall(x))};
    if (h === "exists") throw unsup("existential quantifier");
    if (h === "if") {
      const k = x.indexOf("then");
      if (k < 0) throw unsup("unsupported formula form: if without then");
      const conds = x.slice(1, k).map(parse);
      const cons = x.slice(k + 1).map(parse);
      const clits = cons.filter(c => c.t === "lit");
      const cblocks = cons.filter(c => c.t === "block");
      let head;
      if (cblocks.length) {
        if (clits.length !== 1 || clits.length + cblocks.length !== cons.length) {
          throw unsup("unsupported formula form: if-then with several heads and $block");
        }
        head = {t: "or", parts: clits.concat(cblocks)};
      } else head = cons.length === 1 ? cons[0] : {t: "and", parts: cons};
      return {t: "imp", a: conds.length === 1 ? conds[0] : {t: "and", parts: conds}, b: head};
    }
    const ops = [];
    for (let i = 1; i < x.length; i += 2) if (typeof x[i] === "string" && CONNECTIVES.has(x[i])) ops.push(x[i]);
    if (ops.length && ops.length === Math.floor((x.length - 1) / 2) && x.length % 2 === 1) {
      const parts = [];
      for (let i = 0; i < x.length; i += 2) parts.push(parse(x[i]));
      if (new Set(ops).size !== 1) throw unsup("unsupported formula form: mixed connectives");
      const op = ops[0];
      if (op === "&" || op === "and") return {t: "and", parts: parts};
      if (op === "|" || op === "or") return {t: "or", parts: parts};
      if (parts.length !== 2) throw unsup("unsupported formula form: chained " + op);
      if (op === "=>") return {t: "imp", a: parts[0], b: parts[1]};
      if (op === "<=") return {t: "imp", a: parts[1], b: parts[0]};
      if (op === "<=>") return {t: "iff", a: parts[0], b: parts[1]};
      throw unsup("unsupported formula form: connective " + op);
    }
    if (x.every(e => Array.isArray(e))) return {t: "or", parts: x.map(parse)};
    throw unsup("unsupported formula form: " + cpSlice(pyJsonDumps(x), 60));
  }

  function negLit(l) { return {t: "lit", sign: 1 - l.sign, pred: l.pred, args: l.args}; }

  // nnf
  function nnf(a, neg) {
    const t = a.t;
    if (t === "lit") return neg ? negLit(a) : a;
    if (t === "block") {
      if (neg) throw unsup("unsupported formula form: negated $block");
      return a;
    }
    if (t === "not") return nnf(a.a, !neg);
    if (t === "forall") {
      if (neg) throw unsup("existential quantifier");
      return nnf(a.a, neg);
    }
    if (t === "and" || t === "or") {
      const k = !neg ? t : (t === "and" ? "or" : "and");
      return {t: k, parts: a.parts.map(p => nnf(p, neg))};
    }
    if (t === "imp") return nnf({t: "or", parts: [{t: "not", a: a.a}, a.b]}, neg);
    if (t === "iff") return nnf({t: "and", parts: [{t: "imp", a: a.a, b: a.b}, {t: "imp", a: a.b, b: a.a}]}, neg);
    throw unsup("unsupported formula form");
  }

  // cnf: a list of clauses, each a list of lit and block nodes
  function cnf(a) {
    const t = a.t;
    if (t === "lit" || t === "block") return [[a]];
    if (t === "and") {
      const out = [];
      for (const p of a.parts) for (const c of cnf(p)) out.push(c);
      return out;
    }
    if (t === "or") {
      let acc = [[]];
      for (const p of a.parts) {
        const cs = cnf(p);
        const next = [];
        for (const x of acc) for (const y of cs) next.push(x.concat(y));
        acc = next;
        if (acc.length > 1000) throw unsup("unsupported formula form: clausification too large");
      }
      return acc;
    }
    throw unsup("unsupported formula form");
  }

  // body_lits
  function bodyLits(a) {
    if (a.t === "lit") return [a];
    if (a.t === "and" && a.parts.every(p => p.t === "lit")) return a.parts.slice();
    return null;
  }

  // head_chain
  function headChain(a) {
    if (a.t === "lit") return [a, []];
    if (a.t === "or") {
      const leaves = [];
      const flat = p => {
        if (p.t === "or") { for (const q of p.parts) flat(q); } else leaves.push(p);
      };
      flat(a);
      const lits = leaves.filter(p => p.t === "lit");
      const blocks = leaves.filter(p => p.t === "block");
      if (lits.length === 1 && lits.length + blocks.length === leaves.length) return [lits[0], blocks];
    }
    return null;
  }

  // A proto-clause: {lits: [[sign, pred, args]], blocks: [[strength, [sign, pred, args]]], head}.
  function plain(l) { return [l.sign, l.pred, l.args]; }

  // statement_clauses
  function statementClauses(logic, dirhead) {
    let x = logic;
    while (Array.isArray(x) && x.length === 3 && x[0] === "forall") x = bindForall(x);
    if (dirhead instanceof PInt && Array.isArray(x) && x.length && Array.isArray(x[0])) {
      const items = x.map(parse);
      const lits = items.filter(e => e.t === "lit");
      const blocks = items.filter(e => e.t === "block");
      if (lits.length + blocks.length !== items.length) throw unsup("unsupported formula form: @dirhead list");
      const dh = dirhead.n;
      if (!(dh >= 0 && dh < items.length) || items[dh].t !== "lit") {
        throw unsup("unsupported formula form: @dirhead index");
      }
      const litIdx = [];
      items.forEach((e, i) => { if (e.t === "lit") litIdx.push(i); });
      return [{lits: lits.map(plain), blocks: blocks.map(b => [b.st, plain(b.lit)]), head: litIdx.indexOf(dh)}];
    }
    let a = parse(x);
    while (a.t === "forall") a = a.a;
    let rule = null;
    if (a.t === "imp") {
      const body = bodyLits(a.a);
      const hc = headChain(a.b);
      if (body !== null && hc !== null) rule = [body, hc[0], hc[1]];
    }
    if (rule) {
      const [body, head, blocks] = rule;
      const lits = body.map(l => plain(negLit(l))).concat([plain(head)]);
      return [{lits: lits, blocks: blocks.map(b => [b.st, plain(b.lit)]), head: lits.length - 1}];
    }
    const out = [];
    for (const c of cnf(nnf(a, false))) {
      const lits = c.filter(e => e.t === "lit").map(plain);
      const blocks = c.filter(e => e.t === "block").map(e => [e.st, plain(e.lit)]);
      out.push({lits: lits, blocks: blocks, head: lits.length === 1 ? 0 : null});
    }
    return out;
  }

  // ---------------------------------------------------------------- statements and the question

  function mget(m, k, dflt) { return m.has(k) ? m.get(k) : dflt; }

  // confidence_of
  function confidenceOf(st) {
    const c = st instanceof Map ? mget(st, "@confidence", 1.0) : 1.0;
    if (c instanceof PInt) {
      if (!(c.n >= 0 && c.n <= 100)) throw unsup("unsupported confidence " + pyRepr(c));
      return c.n / 100.0;
    }
    if (typeof c !== "number") throw unsup("unsupported confidence " + pyRepr(c));
    if (!(c >= 0 && c <= 1)) throw unsup("unsupported confidence " + pyRepr(c));
    return c;
  }

  // question_literal
  function questionLiteral(f) {
    const l = !(Array.isArray(f) && f.length && Array.isArray(f[0])) ? litOf(f) : null;
    if (l) return [l.sign, l.pred, l.args];
    let a;
    try { a = parse(f); } catch (e) {
      if (e instanceof Unsupported) throw unsup("compound question");
      throw e;
    }
    const s = pyJsonDumps(f);
    if (a.t === "imp" || s.indexOf('"if"') >= 0 || s.indexOf('"=>"') >= 0 || s.indexOf('"<="') >= 0) {
      throw unsup("conditional question");
    }
    throw unsup("compound question");
  }

  // has_equality
  function hasEquality(x) {
    if (typeof x === "string") return x === "=" || x === "!=" || x === "-=";
    if (Array.isArray(x)) return x.some(hasEquality);
    return false;
  }

  function isAnsLit(e) { return Array.isArray(e) && e.length && e[0] === "$ans"; }

  // classify
  function classify(stmts) {
    const clauses = [], questions = [];
    for (const st of stmts) {
      const f = st instanceof Map ? mget(st, "@logic", mget(st, "@question", null)) : st;
      if (hasEquality(f)) throw unsup("equality");
    }
    for (let si = 0; si < stmts.length; si++) {
      const st = stmts[si];
      let logic, role, dirhead;
      if (st instanceof Map) {
        if (st.has("@report") || st.has("@marginal")) throw unsup("@report or @marginal declaration");
        if (st.has("@question")) {
          questions.push(questionLiteral(st.get("@question")));
          continue;
        }
        if (!st.has("@logic")) throw unsup("JSON-LD structure");
        role = mget(st, "@role", null);
        logic = st.get("@logic");
        if (role === "question" || role === "conjecture") {
          questions.push(questionLiteral(logic));
          continue;
        }
        dirhead = mget(st, "@dirhead", null);
      } else {
        logic = st; role = null; dirhead = null;
      }
      const conf = confidenceOf(st);
      if (conf === 0) continue;
      if (Array.isArray(logic) && logic.length && Array.isArray(logic[0]) && logic.some(isAnsLit)) {
        const rest = logic.filter(e => !isAnsLit(e));
        if (rest.length !== 1) throw unsup("compound question");
        const l = litOf(rest[0]);
        if (!l) throw unsup("compound question");
        questions.push([1 - l.sign, l.pred, l.args]);
        continue;
      }
      if (role === "negated_conjecture") {
        const l = litOf(logic);
        if (!l) throw unsup("compound question");
        questions.push([1 - l.sign, l.pred, l.args]);
        continue;
      }
      const pcs = statementClauses(logic, dirhead);
      if (pcs.length > 1 && conf < 1) throw unsup("uncertain formula with several clauses");
      for (const pc of pcs) clauses.push([si, conf, pc]);
    }
    if (!questions.length) throw unsup("no question");
    if (questions.length > 1) throw unsup("several questions");
    return [clauses, questions[0]];
  }

  // ---------------------------------------------------------------- grounding

  function isNum(t) { return typeof t !== "string" && (t.tag === "i" || t.tag === "r"); }

  // builtin_value
  function builtinValue(pred, args) {
    if (pred === "$less" || pred === "$greater" || pred === "$lessorequal" || pred === "$greaterorequal") {
      if (args.length !== 2 || !(isNum(args[0]) && isNum(args[1]))) {
        throw unsup("unknown built-in: " + pred + " on non-numbers");
      }
      const a = args[0].num, b = args[1].num;
      if (pred === "$less") return a < b;
      if (pred === "$greater") return a > b;
      if (pred === "$lessorequal") return a <= b;
      return a >= b;
    }
    if (pred === "$is_int") return args.length === 1 && args[0].tag === "i";
    if (pred === "$is_real") return args.length === 1 && args[0].tag === "r";
    if (pred === "$is_number") return args.length === 1 && isNum(args[0]);
    throw unsup("unknown built-in: " + pred);
  }

  function isBuiltin(pred) { return pred.startsWith("$") && !ORDINARY_DOLLAR.has(pred); }

  // constants_of: sorted by (tag, str(value))
  function constantsOf(clauses, qlit) {
    const cs = new Set();
    const add = args => { for (const a of args || []) if (typeof a !== "string") cs.add(a); };
    for (const [, , pc] of clauses) {
      for (const l of pc.lits) add(l[2]);
      for (const b of pc.blocks) add(b[1][2]);
    }
    add(qlit[2]);
    return Array.from(cs).sort((a, b) => (a.tag < b.tag ? -1 : (a.tag > b.tag ? 1 : cmpStr(a.str, b.str))));
  }

  function uniq(xs) {
    const out = [];
    for (const x of xs) if (out.indexOf(x) < 0) out.push(x);
    return out;
  }

  // clause_vars: (in ordinary literals, only in built-in literals, only in exception literals)
  function clauseVars(pc) {
    let ordv = [], bv = [], ev = [];
    for (const [, p, args] of pc.lits) {
      for (const a of args || []) if (typeof a === "string") (isBuiltin(p) ? bv : ordv).push(a);
    }
    for (const [, l] of pc.blocks) for (const a of l[2] || []) if (typeof a === "string") ev.push(a);
    ordv = uniq(ordv);
    bv = uniq(bv).filter(a => ordv.indexOf(a) < 0);
    ev = uniq(ev).filter(a => ordv.indexOf(a) < 0 && bv.indexOf(a) < 0);
    return [ordv, bv, ev];
  }

  // itertools.product(consts, repeat=k), the last position fastest
  function* product(consts, k) {
    if (k === 0) { yield []; return; }
    if (!consts.length) return;
    const ix = new Array(k).fill(0);
    while (true) {
      yield ix.map(i => consts[i]);
      let p = k - 1;
      while (p >= 0) {
        ix[p]++;
        if (ix[p] < consts.length) break;
        ix[p] = 0;
        p--;
      }
      if (p < 0) return;
    }
  }

  function groundLit(l, sub) {
    const args = l[2];
    if (args === null) return [l[0], l[1], null];
    return [l[0], l[1], args.map(a => (typeof a === "string" && sub.has(a)) ? sub.get(a) : a)];
  }

  function litCode(gl) { return atomOf(gl[1], gl[2]).id * 2 + gl[0]; }

  // ground: (statement index, conf, literal codes, blocks [strength, code], head)
  function ground(clauses, consts, maxGround) {
    let total = 0;
    for (const [, , pc] of clauses) {
      const [ordv, bv, ev] = clauseVars(pc);
      if (bv.length) throw unsup("built-in over an open domain");
      total += Math.pow(consts.length, ordv.length + ev.length);
      if (total > maxGround) throw unsup("grounding limit");
    }
    const out = [];
    for (const [si, conf, pc] of clauses) {
      const [vs, , ev] = clauseVars(pc);
      const etuples = ev.length ? Array.from(product(consts, ev.length)) : [[]];
      const seen = new Set();
      for (const tup of product(consts, vs.length)) {
        const sub = new Map();
        vs.forEach((v, k) => sub.set(v, tup[k]));
        const lits = pc.lits.map(l => groundLit(l, sub));
        const blocks = [], bseen = new Set();
        for (const et of etuples) {
          const esub = new Map(sub);
          ev.forEach((v, k) => esub.set(v, et[k]));
          for (const [st, l] of pc.blocks) {
            const gl = groundLit(l, esub);
            const code = litCode(gl);
            const bk = st + ":" + code;
            if (!bseen.has(bk)) { bseen.add(bk); blocks.push([st, code, gl[1]]); }
          }
        }
        const head = pc.head;
        const keep = [];
        let drop = false;
        for (let i = 0; i < lits.length; i++) {
          const l = lits[i];
          if (isBuiltin(l[1])) {
            if (head !== null && i === head) throw unsup("unknown built-in: " + l[1] + " as a head");
            const cond = builtinValue(l[1], l[2] || []);   // the condition is the complement of the clause literal
            const trueCond = l[0] === 1 ? cond : !cond;
            if (trueCond) continue;
            drop = true;
            break;
          }
          keep.push(l);
        }
        if (drop) continue;
        for (const b of blocks) if (isBuiltin(b[2])) throw unsup("unknown built-in: " + b[2] + " in an exception");
        if (!keep.length) throw unsup("empty ground clause");
        const hl = head !== null ? litCode(lits[head]) : null;
        const kc = uniq(keep.map(litCode));
        const nh = (hl !== null && kc.indexOf(hl) >= 0) ? kc.indexOf(hl) : null;
        const key = kc.join(",") + "|" + blocks.map(b => b[0] + ":" + b[1]).join(",") + "|" + nh;
        if (seen.has(key)) continue;
        seen.add(key);
        out.push([si, conf, kc, blocks.map(b => [b[0], b[1]]), nh]);
      }
    }
    return out;
  }

  // read_input
  function readInput(text, opts, maxGround, files) {
    const inp = {convertedBy: null, question: null, qvars: [], constants: [], ground: []};
    const conv = [];
    let stmts;
    try {
      stmts = readStatements(text, opts, conv, files, opts, 0);
    } finally {
      inp.convertedBy = conv.length ? conv[0] : null;
    }
    const [clauses, q] = classify(stmts);
    inp.question = q;
    const [, qp, qargs] = q;
    for (const a of qargs || []) if (isVar(a) && inp.qvars.indexOf(a) < 0) inp.qvars.push(a);
    if (isBuiltin(qp) || qp === "=" || qp === "!=") {
      throw unsup((qp === "=" || qp === "!=") ? "equality" : "unknown built-in: " + qp + " in the question");
    }
    inp.constants = constantsOf(clauses, q);
    const hasVars = inp.qvars.length > 0 || clauses.some(([, , pc]) => clauseVars(pc).some(v => v.length));
    if (hasVars && !inp.constants.length) throw unsup("no constants");
    inp.ground = ground(clauses, inp.constants, maxGround);
    return inp;
  }

  // ---------------------------------------------------------------- applications (mcref.py)
  //
  // An application: {head (atom), hsign, body (literal codes), exc (literal
  // codes), conf, normal, rank, kind, crank}.

  // application
  function application(h, body, excs, strength, conf, crank, flat) {
    const head = atomList[h >> 1], sign = h & 1;
    const comp = h ^ 1;
    if (excs.indexOf(comp) >= 0) {
      return {head: head, hsign: sign, body: body, exc: excs.filter(e => e !== comp), conf: conf, normal: true,
        rank: strength.get(comp), kind: "normal default", crank: crank};
    }
    if (excs.length) {
      return {head: head, hsign: sign, body: body, exc: excs.slice(), conf: conf, normal: false, rank: 0,
        kind: "default", crank: crank};
    }
    return {head: head, hsign: sign, body: body, exc: [], conf: conf, normal: false, rank: 0,
      kind: !body.length ? "fact" : (flat ? "classical" : "directed"), crank: 0};
  }

  // app_text
  function appText(x) {
    let t = litText(x.hsign, x.head.pred, x.head.args);
    if (x.body.length) t += " <- " + x.body.map(codeText).join(", ");
    if (x.exc.length) t += " [unless " + x.exc.map(codeText).join(", ") + "]";
    return t;
  }

  // orient
  function orient(gclauses) {
    const apps = [], dropped = [];
    let nsrc = 0;
    const keep = (x, si) => {
      const same = x.exc.filter(e => x.body.indexOf(e) >= 0);
      if (same.length) dropped.push([si, x, same[0]]);
      else apps.push(x);
    };
    for (const gc of gclauses) {
      const si = gc[0], conf = gc[1], lits = gc[2], blocks = gc[3];
      let head = gc[4];
      const excs = uniq(blocks.map(b => b[1]));
      const strength = new Map();
      for (const [st, k] of blocks) strength.set(k, Math.max(strength.has(k) ? strength.get(k) : 0, st));
      let crank = 0;
      if (strength.size) {
        crank = -Infinity;
        for (const v of strength.values()) if (v > crank) crank = v;
      }
      if (lits.length === 1) head = 0;
      if (head !== null && lits.length > 1 && conf >= 1 && !blocks.length) head = null;
      if (head !== null) {
        const h = lits[head];
        const body = uniq(lits.filter((l, i) => i !== head).map(l => l ^ 1));
        keep(application(h, body, excs, strength, conf, crank, false), si);
        continue;
      }
      let extra = [], c2 = conf;
      if (conf < 1) {
        nsrc++;
        const src = atomOf("$src_" + nsrc, []);
        apps.push({head: src, hsign: 0, body: [], exc: [], conf: conf, normal: false, rank: 0,
          kind: "source event", crank: 0});
        extra = [src.id * 2];
        c2 = 1.0;
      }
      for (let i = 0; i < lits.length; i++) {
        const body = uniq(lits.filter((l, j) => j !== i).map(l => l ^ 1).concat(extra));
        keep(application(lits[i], body, excs, strength, c2, crank, true), si);
      }
    }
    return [apps, dropped];
  }

  // ---------------------------------------------------------------- static passes before sampling

  function byheadOf(byhead, a) { return byhead.get(a.id) || []; }

  // closure: the atoms the start atoms depend on, through bodies and exceptions
  function closure(starts, byhead) {
    const seen = new Set(), todo = starts.slice();
    while (todo.length) {
      const a = todo.pop();
      if (seen.has(a)) continue;
      seen.add(a);
      for (const x of byheadOf(byhead, a)) {
        for (const c of x.body) { const b = atomList[c >> 1]; if (!seen.has(b)) todo.push(b); }
        for (const c of x.exc) { const b = atomList[c >> 1]; if (!seen.has(b)) todo.push(b); }
      }
    }
    return seen;
  }

  // the order of atom texts: sorted(atoms, key=(atom_text, args is None))
  function sortAtoms(atoms) {
    return Array.from(atoms).sort((a, b) => {
      const c = cmpStr(a.text, b.text);
      if (c) return c;
      return (a.none ? 1 : 0) - (b.none ? 1 : 0);
    });
  }

  function sortedUniqInts(xs) {
    return Array.from(new Set(xs)).sort((a, b) => a - b);
  }

  // by_components
  function byComponents(atoms, byhead, own, combine) {
    const order = sortAtoms(atoms);
    const idx = new Map();
    order.forEach((k, i) => idx.set(k.id, i));
    const deps = order.map(a => {
      const js = [];
      for (const x of byheadOf(byhead, a)) {
        for (const c of x.body) js.push(idx.get(c >> 1));
        for (const c of x.exc) js.push(idx.get(c >> 1));
      }
      return sortedUniqInts(js);
    });
    const val = new Array(order.length).fill(null);
    for (const nodes of components(deps, order.length)) {
      const members = new Set(nodes);
      let v = null;
      for (const i of nodes) {
        v = combine(v, own(order[i]));
        for (const j of deps[i]) if (!members.has(j)) v = combine(v, val[j]);
      }
      for (const i of nodes) val[i] = v;
    }
    const out = new Map();
    order.forEach((a, i) => out.set(a.id, val[i]));
    return out;
  }

  // lower: values are [rank, text]
  function lower(a, b) {
    return (a === null || (b !== null && b[0] < a[0])) ? b : a;
  }

  // rank_contexts
  function rankContexts(atoms, byhead) {
    const ownMin = a => {
      let best = null;
      for (const x of byheadOf(byhead, a)) {
        if (!(x.crank > 0)) continue;
        const r = [x.crank, litText(x.hsign, x.head.pred, x.head.args)];
        if (best === null || r[0] < best[0] || (r[0] === best[0] && cmpStr(r[1], best[1]) < 0)) best = r;
      }
      return best;
    };
    const low = byComponents(atoms, byhead, ownMin, lower);
    const bad = new Map();
    for (const a of atoms) {
      for (const x of byheadOf(byhead, a)) {
        if (x.crank > 0 && x.exc.length) {
          for (const c of x.exc) {
            const m = low.has(c >> 1) ? low.get(c >> 1) : null;
            if (m !== null && m[0] < x.crank && !bad.has(a.id)) {
              bad.set(a.id, "rank contexts: a rank-" + m[0] + " default for " + m[1] + " inside a rank-" +
                x.crank + " exception check");
            }
          }
        }
      }
    }
    const all = byComponents(atoms, byhead, a => (bad.has(a.id) ? bad.get(a.id) : null),
      (u, w) => (u !== null ? u : w));
    const out = new Map();
    for (const [k, v] of all) if (v !== null) out.set(k, v);
    return out;
  }

  // reachable: the possible literals (codes), a least fixpoint over the applications
  function reachable(apps) {
    const possible = new Set(), waiting = new Map(), need = new Array(apps.length);
    const todo = [];
    apps.forEach((x, i) => {
      need[i] = x.body.length;
      for (const lit of x.body) {
        if (!waiting.has(lit)) waiting.set(lit, []);
        waiting.get(lit).push(i);
      }
      if (!x.body.length) todo.push(i);
    });
    while (todo.length) {
      const x = apps[todo.pop()];
      const lit = x.head.id * 2 + x.hsign;
      if (possible.has(lit)) continue;
      possible.add(lit);
      for (const j of waiting.get(lit) || []) {
        need[j]--;
        if (need[j] === 0) todo.push(j);
      }
    }
    return possible;
  }

  // components: Tarjan's algorithm, iterative, dependencies first
  function components(deps, n) {
    const index = new Array(n).fill(null), low = new Array(n).fill(0), onst = new Array(n).fill(false);
    const st = [], out = [];
    let c = 0;
    for (let root = 0; root < n; root++) {
      if (index[root] !== null) continue;
      const work = [[root, 0]];
      while (work.length) {
        const [h, i] = work.pop();
        if (i === 0) {
          index[h] = low[h] = c;
          c++;
          st.push(h);
          onst[h] = true;
        }
        if (i < deps[h].length) {
          work.push([h, i + 1]);
          const j = deps[h][i];
          if (index[j] === null) work.push([j, 0]);
          else if (onst[j]) low[h] = Math.min(low[h], index[j]);
          continue;
        }
        if (low[h] === index[h]) {
          const comp = [];
          while (true) {
            const j = st.pop();
            onst[j] = false;
            comp.push(j);
            if (j === h) break;
          }
          out.push(comp.sort((a, b) => a - b));
        }
        if (work.length) {
          const w = work[work.length - 1][0];
          low[w] = Math.min(low[w], low[h]);
        }
      }
    }
    return out;
  }

  // ---------------------------------------------------------------- the tables (memo 4.2, 4.4)
  //
  // An evaluated application: {hs, q (1 - confidence), body, exc, normal,
  // rank}; body and exception entries are the codes 2 * atom index + state,
  // with POS = 0 and NEG = 1.

  // rows
  function rows(np, nn, ordp, ordn, rp, rn, a, b, u, v) {
    if (!np && !nn) return IGN;
    if (!nn) return u < a ? POS : IGN;
    if (!np) return u < b ? NEG : IGN;
    const normp = ordp === 0, normn = ordn === 0;
    if (!normp && !normn) {
      if (b <= u && u < a) return POS;
      if (a <= u && u < b) return NEG;
      return u < Math.min(a, b) ? CON : IGN;
    }
    if (normp && !normn) return u < b ? NEG : (v < a ? POS : IGN);
    if (normn && !normp) return u < a ? POS : (v < b ? NEG : IGN);
    if (rp === rn || rp === 0 || rn === 0) {
      const p = u < a, q = v < b;
      return (p && !q) ? POS : ((q && !p) ? NEG : IGN);
    }
    if (rp > rn) return u < a ? POS : (u < b ? NEG : IGN);
    return u < b ? NEG : (u < a ? POS : IGN);
  }

  // outcome: from the final states of the atoms an atom reads
  function outcome(apps, state, u, v) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0, ordp = 0, ordn = 0, rp = 0, rn = 0;
    for (let k = 0; k < apps.length; k++) {
      const x = apps[k];
      let ok = true;
      const body = x.body;
      for (let m = 0; m < body.length; m++) {
        const c = body[m];
        if (state[c >> 1] !== (c & 1)) { ok = false; break; }
      }
      if (ok) {
        const exc = x.exc;
        for (let m = 0; m < exc.length; m++) {
          const c = exc[m];
          if (state[c >> 1] === (c & 1)) { ok = false; break; }
        }
      }
      if (!ok) continue;
      if (x.hs === 0) {
        np++;
        ra *= x.q;
        if (x.normal) rp = Math.max(rp, x.rank); else ordp++;
      } else {
        nn++;
        rb *= x.q;
        if (x.normal) rn = Math.max(rn, x.rank); else ordn++;
      }
    }
    return rows(np, nn, ordp, ordn, rp, rn, 1.0 - ra, 1.0 - rb, u, v);
  }

  function allIn(lits, set) {
    for (let m = 0; m < lits.length; m++) if (!set.has(lits[m])) return false;
    return true;
  }

  function anyIn(lits, set) {
    for (let m = 0; m < lits.length; m++) if (set.has(lits[m])) return true;
    return false;
  }

  // outcome_sets: bodies in bset, no exception in eset
  function outcomeSets(apps, u, v, bset, eset) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0, ordp = 0, ordn = 0, rp = 0, rn = 0;
    for (const x of apps) {
      if (!allIn(x.body, bset) || anyIn(x.exc, eset)) continue;
      if (x.hs === 0) {
        np++;
        ra *= x.q;
        if (x.normal) rp = Math.max(rp, x.rank); else ordp++;
      } else {
        nn++;
        rb *= x.q;
        if (x.normal) rn = Math.max(rn, x.rank); else ordn++;
      }
    }
    return rows(np, nn, ordp, ordn, rp, rn, 1.0 - ra, 1.0 - rb, u, v);
  }

  // ---------------------------------------------------------------- the narrowing (memo 5.5)
  //
  // Sets hold literal codes. X is the set being built, L the old sure set,
  // U the old possible set. An atom's applications are an object {all, side:
  // [for POS, for NEG], anyNormal, ord}; ord is the same object for the
  // ordinary applications only.

  // wf_side_usable
  function wfSideUsable(sign, apps, uVal, vVal, bodyOwn, excOwn, bodyOpp, excOpp) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0;
    for (const x of apps) {
      let bset, eset;
      if (x.hs === sign) { bset = bodyOwn; eset = excOwn; } else { bset = bodyOpp; eset = excOpp; }
      if (!allIn(x.body, bset) || anyIn(x.exc, eset)) continue;
      if (x.hs === 0) { np++; ra *= x.q; } else { nn++; rb *= x.q; }
    }
    if (sign === 0) {
      if (!np) return false;
      const a = 1.0 - ra;
      return !nn ? (uVal < a) : ((1.0 - rb) <= uVal && uVal < a);
    }
    if (!nn) return false;
    const b = 1.0 - rb;
    return !np ? (uVal < b) : ((1.0 - ra) <= uVal && uVal < b);
  }

  // side_regimes: [present, normal, rank, least support, largest support]
  function sideRegimes(appsSide, bmin, emax, bmax, emin, requireNonemptyMin) {
    const sMin = [], sMax = [];
    for (const x of appsSide) {
      const inMax = allIn(x.body, bmax) && !anyIn(x.exc, emin);
      if (!inMax) continue;
      sMax.push(x);
      if (bmin !== null && allIn(x.body, bmin) && !anyIn(x.exc, emax)) sMin.push(x);
    }
    const regs = [];
    if (!sMin.length && !requireNonemptyMin) regs.push([false, false, 0, 0.0, 0.0]);
    if (!sMax.length) return regs;
    let rSmin = 1.0, minHasOrd = false;
    for (const x of sMin) {
      rSmin *= x.q;
      if (!x.normal) minHasOrd = true;
    }
    const sMinIds = new Set(sMin);
    const maxOrds = sMax.filter(x => !x.normal);
    if (maxOrds.length) {
      let rSmax = 1.0;
      for (const x of sMax) rSmax *= x.q;
      let rOrdMax;
      if (minHasOrd) rOrdMax = rSmin;
      else {
        let m = -Infinity;
        for (const x of maxOrds) if (!sMinIds.has(x) && x.q > m) m = x.q;
        rOrdMax = rSmin * m;
      }
      regs.push([true, false, 0, 1.0 - rOrdMax, 1.0 - rSmax]);
    }
    if (!minHasOrd) {
      const nMax = sMax.filter(x => x.normal);
      if (nMax.length) {
        let rBase = null;
        for (const x of sMin) if (rBase === null || x.rank > rBase) rBase = x.rank;
        const ranks = sortedUniqInts(nMax.filter(x => rBase === null || x.rank >= rBase).map(x => x.rank));
        for (const rk of ranks) {
          let rRkMin = 1.0;
          for (const x of nMax) if (x.rank <= rk) rRkMin *= x.q;
          let rRkMax;
          if (rBase !== null && rk === rBase) rRkMax = rSmin;
          else {
            let m = -Infinity;
            for (const x of nMax) if (x.rank === rk && !sMinIds.has(x) && x.q > m) m = x.q;
            rRkMax = rSmin * m;
          }
          regs.push([true, true, rk, 1.0 - rRkMax, 1.0 - rRkMin]);
        }
      }
    }
    return regs;
  }

  // row_side_holds
  function rowSideHolds(sign, pOwn, normOwn, rOwn, aOwn, pOpp, normOpp, rOpp, bOpp, uVal, vVal) {
    if (!pOwn) return false;
    if (!pOpp) return uVal < aOwn;
    if (sign === 0) {
      const a = aOwn, b = bOpp, normp = normOwn, normn = normOpp, rp = rOwn, rn = rOpp;
      if (!normp && !normn) return b <= uVal && uVal < a;
      if (normp && !normn) return (uVal >= b) && (vVal < a);
      if (normn && !normp) return uVal < a;
      if (rp === rn || rp === 0 || rn === 0) return (uVal < a) && (vVal >= b);
      if (rp > rn) return uVal < a;
      return b <= uVal && uVal < a;
    }
    const a = bOpp, b = aOwn, normp = normOpp, normn = normOwn, rp = rOpp, rn = rOwn;
    if (!normp && !normn) return a <= uVal && uVal < b;
    if (normp && !normn) return uVal < b;
    if (normn && !normp) return (uVal >= a) && (vVal < b);
    if (rp === rn || rp === 0 || rn === 0) return (vVal < b) && (uVal >= a);
    if (rp > rn) return a <= uVal && uVal < b;
    return uVal < b;
  }

  // env_surely_usable
  function envSurelyUsable(sign, AA, uVal, vVal, X, L, U) {
    if (!AA.anyNormal) return wfSideUsable(sign, AA.all, uVal, vVal, X, U, U, L);
    const own = AA.side[sign];
    let any = false;
    for (const x of own) if (allIn(x.body, X) && !anyIn(x.exc, U)) { any = true; break; }
    if (!any) return false;
    const opp = AA.side[1 - sign];
    const ownRegs = sideRegimes(own, X, U, U, L, false);
    const oppRegs = sideRegimes(opp, L, U, U, L, false);
    for (const o of ownRegs) {
      for (const p of oppRegs) {
        if (!rowSideHolds(sign, o[0], o[1], o[2], o[3], p[0], p[1], p[2], p[4], uVal, vVal)) return false;
      }
    }
    return true;
  }

  // env_possibly_usable
  function envPossiblyUsable(sign, AA, uVal, vVal, X, L, U) {
    if (!AA.anyNormal) return wfSideUsable(sign, AA.all, uVal, vVal, X, L, L, U);
    const own = AA.side[sign];
    const ownRegs = sideRegimes(own, null, null, X, L, true);
    if (!ownRegs.length) return false;
    const opp = AA.side[1 - sign];
    const oppRegs = sideRegimes(opp, L, U, U, L, false);
    for (const o of ownRegs) {
      for (const p of oppRegs) {
        if (rowSideHolds(sign, o[0], o[1], o[2], o[4], p[0], p[1], p[2], p[3], uVal, vVal)) return true;
      }
    }
    return false;
  }

  // wf_lfp_sure and wf_lfp_poss
  function wfLfp(sure, active, ext, byatom, ordOnly, u, v, L, U) {
    const X = new Set(ext);
    const test = sure ? envSurelyUsable : envPossiblyUsable;
    while (true) {
      let added = false;
      for (const i of active) {
        const AA = ordOnly ? byatom[i].ord : byatom[i];
        if (!X.has(2 * i) && test(0, AA, u[i], v[i], X, L, U)) { X.add(2 * i); added = true; }
        if (!X.has(2 * i + 1) && test(1, AA, u[i], v[i], X, L, U)) { X.add(2 * i + 1); added = true; }
      }
      if (!added) return X;
    }
  }

  function setEq(a, b) {
    if (a.size !== b.size) return false;
    for (const x of a) if (!b.has(x)) return false;
    return true;
  }

  // is_cross_sign
  function isCrossSign(nodes, byatom) {
    const members = new Set(nodes);
    const sg = [false, false];
    for (const h of nodes) {
      for (const x of byatom[h].all) {
        const inside = x.body.filter(c => members.has(c >> 1));
        if (inside.length) {
          sg[x.hs] = true;
          if (inside.some(c => (c & 1) !== x.hs)) return true;
        }
      }
    }
    return sg[0] && sg[1];
  }

  // run_narrow_stage
  function runNarrowStage(nodes, extBase, unresLits, locked, byatom, ordOnly, u, v) {
    let sweeps = 0;
    while (true) {
      const ext = new Set(extBase);
      for (const [ki, kst] of locked) {
        if (kst === POS) ext.add(2 * ki);
        else if (kst === NEG) ext.add(2 * ki + 1);
      }
      const active = nodes.filter(i => !locked.has(i));
      const extPoss = new Set(ext);
      for (const x of unresLits) extPoss.add(x);
      let L = new Set(ext);
      let U = new Set(extPoss);
      for (const i of active) { U.add(2 * i); U.add(2 * i + 1); }
      while (true) {
        sweeps++;
        const nL = wfLfp(true, active, ext, byatom, ordOnly, u, v, L, U);
        const nU = wfLfp(false, active, extPoss, byatom, ordOnly, u, v, nL, U);
        if (setEq(nL, L) && setEq(nU, U)) break;
        L = nL;
        U = nU;
      }
      const newConf = active.filter(i => !L.has(2 * i) && !L.has(2 * i + 1) &&
        outcomeSets((ordOnly ? byatom[i].ord : byatom[i]).all, u[i], v[i], U, L) === CON);
      if (!newConf.length) return [L, U, sweeps];
      for (const i of newConf) locked.set(i, CON);
    }
  }

  // narrow_group
  function narrowGroup(g, byatom, u, v, state, unresReading, stats) {
    const nodes = g.nodes;
    const extBase = new Set(), unresLits = new Set();
    for (const j of g.outside) {
      if (state[j] === POS) extBase.add(2 * j);
      else if (state[j] === NEG) extBase.add(2 * j + 1);
      else if (state[j] === UNRES) { unresLits.add(2 * j); unresLits.add(2 * j + 1); }
    }
    const locked = new Map();
    let sw1 = 0;
    if (g.hasNorm) {
      const r1 = runNarrowStage(nodes, extBase, unresLits, locked, byatom, true, u, v);
      const L1 = r1[0], U1 = r1[1];
      sw1 = r1[2];
      for (const i of nodes) {
        if (!locked.has(i)) {
          if (L1.has(2 * i)) locked.set(i, POS);
          else if (L1.has(2 * i + 1)) locked.set(i, NEG);
          else if (!U1.has(2 * i) && !U1.has(2 * i + 1)) {
            if (outcomeSets(byatom[i].ord.all, u[i], v[i], L1, U1) === CON) locked.set(i, CON);
          }
        }
      }
    }
    const r2 = runNarrowStage(nodes, extBase, unresLits, locked, byatom, false, u, v);
    const L = r2[0], U = r2[1];
    if (sw1 + r2[2] > stats[0]) stats[0] = sw1 + r2[2];
    for (const i of nodes) {
      if (locked.has(i)) state[i] = locked.get(i);
      else if (L.has(2 * i)) state[i] = POS;
      else if (L.has(2 * i + 1)) state[i] = NEG;
      else if (!U.has(2 * i) && !U.has(2 * i + 1)) state[i] = outcomeSets(byatom[i].all, u[i], v[i], L, U);
      else state[i] = unresReading;
    }
  }

  // world: the cycle groups in dependency order
  function world(byatom, comps, inner, u, v, state, stats) {
    for (const g of comps) {
      const nodes = g.nodes;
      let unresOutside = false;
      for (const j of g.outside) if (state[j] === UNRES) { unresOutside = true; break; }
      if (unresOutside) {
        narrowGroup(g, byatom, u, v, state, UNRES, stats);
        continue;
      }
      if (!g.cyclic) {
        const i = nodes[0];
        state[i] = outcome(byatom[i].all, state, u[i], v[i]);
        continue;
      }
      if (!g.cross) {
        // a one-sign or exception-only group: sweeps (memo 5.1); the narrowing
        // only when a sweep repeats a state, an undecided atom then ignorance
        for (const i of nodes) state[i] = IGN;
        let dirty = nodes, settled = false, sw = 0;
        const keyOf = () => {
          let k = "";
          for (const i of nodes) k += state[i];
          return k;
        };
        const seen = new Set([keyOf()]);
        while (true) {
          sw++;
          const changed = [];
          for (const i of dirty) {
            const s = outcome(byatom[i].all, state, u[i], v[i]);
            if (s !== state[i]) changed.push(i, s);
          }
          if (!changed.length) { settled = true; break; }
          const nd = new Set();
          for (let k = 0; k < changed.length; k += 2) {
            state[changed[k]] = changed[k + 1];
            for (const r of inner[changed[k]]) nd.add(r);
          }
          dirty = Array.from(nd).sort((a, b) => a - b);
          const key = keyOf();
          if (seen.has(key)) break;
          if (sw >= SWEEP_CAP) { stats[1]++; break; }
          seen.add(key);
        }
        if (sw > stats[0]) stats[0] = sw;
        if (settled) continue;
        narrowGroup(g, byatom, u, v, state, IGN, stats);
        continue;
      }
      narrowGroup(g, byatom, u, v, state, UNRES, stats);
    }
  }

  // hoeffding and summary
  function hoeffding(n) { return n ? Math.sqrt(Math.log(8 / 0.05) / (2 * n)) : 1.0; }

  function summary(counts, n, swap) {
    const c = counts.slice();
    if (swap) { const t = c[0]; c[0] = c[1]; c[1] = t; }
    const e = hoeffding(n);
    const val = c.slice(0, 4).map(x => x / n);
    return {counts: c, value: val, unstable: c[4] / n,
      interval_95: val.map(p => [Math.max(0.0, p - e), Math.min(1.0, p + e)])};
  }

  // ---------------------------------------------------------------- splitmix64 with 32-bit halves
  //
  // mcref.py computes splitmix64 on Python integers. The port splits each
  // 64-bit number into two 32-bit halves; the values are the same.

  let MH = 0, ML = 0;

  // (ah, al) * (bh, bl) modulo 2^64, into MH and ML
  function mul64(ah, al, bh, bl) {
    const a0 = al & 0xffff, a1 = al >>> 16, b0 = bl & 0xffff, b1 = bl >>> 16;
    const p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
    const mid = (p00 >>> 16) + (p01 & 0xffff) + (p10 & 0xffff);
    ML = (((mid & 0xffff) << 16) | (p00 & 0xffff)) >>> 0;
    const carry = p11 + (p01 >>> 16) + (p10 >>> 16) + (mid >>> 16);
    MH = (carry + Math.imul(ah, bl) + Math.imul(al, bh)) >>> 0;
  }

  // the uniform number of splitmix64 for the state t = (th, tl)
  function mixUniform(th, tl) {
    let zl = (tl ^ ((tl >>> 30) | (th << 2))) >>> 0;
    let zh = (th ^ (th >>> 30)) >>> 0;
    mul64(zh, zl, 0xBF58476D, 0x1CE4E5B9);
    zh = MH; zl = ML;
    zl = (zl ^ ((zl >>> 27) | (zh << 5))) >>> 0;
    zh = (zh ^ (zh >>> 27)) >>> 0;
    mul64(zh, zl, 0x94D049BB, 0x133111EB);
    zh = MH; zl = ML;
    zl = (zl ^ ((zl >>> 31) | (zh << 1))) >>> 0;
    zh = (zh ^ (zh >>> 31)) >>> 0;
    return ((zh >>> 11) * 4294967296 + (((zl >>> 11) | (zh << 21)) >>> 0)) * TWO53;
  }

  const MASK = (BigInt(1) << BigInt(64)) - BigInt(1);
  const GOLDEN = BigInt("0x9E3779B97F4A7C15");

  function halves(b) {
    return [Number(b >> BigInt(32)), Number(b & BigInt(0xffffffff))];
  }

  // ---------------------------------------------------------------- SHA-256 of a text, for the provenance

  function sha256(text) {
    const bytes = new TextEncoder().encode(text);
    const K = new Uint32Array([
      0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]);
    const H = new Uint32Array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
      0x1f83d9ab, 0x5be0cd19]);
    const len = bytes.length;
    const total = Math.ceil((len + 9) / 64) * 64;
    const buf = new Uint8Array(total);
    buf.set(bytes);
    buf[len] = 0x80;
    const bits = len * 8;
    const dv = new DataView(buf.buffer);
    dv.setUint32(total - 8, Math.floor(bits / 4294967296));
    dv.setUint32(total - 4, bits >>> 0);
    const W = new Uint32Array(64);
    const rotr = (x, k) => (x >>> k) | (x << (32 - k));
    for (let off = 0; off < total; off += 64) {
      for (let i = 0; i < 16; i++) W[i] = dv.getUint32(off + 4 * i);
      for (let i = 16; i < 64; i++) {
        const s0 = rotr(W[i - 15], 7) ^ rotr(W[i - 15], 18) ^ (W[i - 15] >>> 3);
        const s1 = rotr(W[i - 2], 17) ^ rotr(W[i - 2], 19) ^ (W[i - 2] >>> 10);
        W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
      }
      let a = H[0], b = H[1], c = H[2], d = H[3], e = H[4], f = H[5], g = H[6], h = H[7];
      for (let i = 0; i < 64; i++) {
        const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        const ch = (e & f) ^ (~e & g);
        const t1 = (h + S1 + ch + K[i] + W[i]) >>> 0;
        const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        const mj = (a & b) ^ (a & c) ^ (b & c);
        const t2 = (S0 + mj) >>> 0;
        h = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = b; b = a; a = (t1 + t2) >>> 0;
      }
      H[0] += a; H[1] += b; H[2] += c; H[3] += d; H[4] += e; H[5] += f; H[6] += g; H[7] += h;
    }
    let out = "";
    for (let i = 0; i < 8; i++) out += hexN(H[i], 8);
    return out;
  }

  // ---------------------------------------------------------------- the run (mcref.py run)

  function mcref(inputText, options) {
    const o = options || {};
    const samples = o.samples === undefined ? 100000 : o.samples;
    const seed = o.seed === undefined ? 1 : o.seed;
    const maxGround = o.maxGround === undefined ? 200000 : o.maxGround;
    const allAtoms = !!o.allAtoms;
    if (!Number.isInteger(samples) || samples < 1) throw new Error("samples must be at least 1");
    if (typeof inputText !== "string") throw new Error("the input must be a text");
    const res = {version: VERSION, input: o.name === undefined ? null : o.name, converted_by: null,
      interpretation: Object.assign({}, INTERPRETATION), question: null, variables: [], constants: null,
      ground_clauses: null, atoms: null, applications: null, evaluated_atoms: null, components: null,
      samples: samples, seed: seed, readings: [], answers: [], unsupported: null,
      provenance: {tool: Object.assign({}, TOOL), files: [["input text", sha256(inputText)]]}};
    const files = res.provenance.files;
    resetTables();
    let inp;
    try {
      inp = readInput(inputText, o, maxGround, files);
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
      res.unsupported = e.message;
      res.converted_by = o.convertedBy ? o.convertedBy : null;
      return res;
    }
    res.converted_by = inp.convertedBy;
    const [qs, qp, qargs] = inp.question;
    res.question = litText(qs, qp, qargs);
    res.variables = inp.qvars.map(a => a.slice(2));
    res.constants = inp.constants.length;
    res.ground_clauses = inp.ground.length;
    const [apps, dropped] = orient(inp.ground);
    res.applications = apps.length;
    res.self_exception_applications = dropped.length;
    const byhead = new Map();
    for (const x of apps) {
      if (!byhead.has(x.head.id)) byhead.set(x.head.id, []);
      byhead.get(x.head.id).push(x);
    }
    // the question's ground instances: [text, atom, binding]
    const insts = [];
    if (inp.qvars.length) {
      for (const tup of product(inp.constants, inp.qvars.length)) {
        const sub = new Map();
        inp.qvars.forEach((a, k) => sub.set(a, tup[k]));
        const args = qargs.map(a => (typeof a === "string" && sub.has(a)) ? sub.get(a) : a);
        const key = findAtom(qp, args);
        if (key && byhead.has(key.id)) insts.push([litText(qs, qp, args), key, tup.map(t => t.out)]);
      }
    } else {
      insts.push([litText(qs, qp, qargs), atomOf(qp, qargs), []]);
    }
    const atoms = new Set();
    for (const x of apps) {
      atoms.add(x.head);
      for (const c of x.body) atoms.add(atomList[c >> 1]);
      for (const c of x.exc) atoms.add(atomList[c >> 1]);
    }
    for (const t of insts) atoms.add(t[1]);
    res.atoms = atoms.size;
    const qatoms = closure(insts.map(t => t[1]), byhead);
    const rc = rankContexts(atoms, byhead);
    const why = insts.filter(t => rc.has(t[1].id)).map(t => rc.get(t[1].id));
    if (why.length) {
      res.unsupported = why[0];
      return res;
    }
    const rel = allAtoms ? atoms : qatoms;
    for (const [si, x, lit] of dropped) {
      if (rel.has(x.head)) {
        res.readings.push(["self exception", "statement " + (si + 1) + ": " + appText(x) + " (exception " +
          codeText(lit) + ")"]);
      }
    }
    const possible = reachable(apps);
    const order = sortAtoms(rel);
    const n = order.length;
    const idx = new Map();
    order.forEach((a, i) => idx.set(a.id, i));
    res.evaluated_atoms = n;
    let lists = [];
    for (let i = 0; i < n; i++) lists.push([]);
    for (const x of apps) {
      if (!idx.has(x.head.id)) continue;
      const h = idx.get(x.head.id);
      const body = x.body.map(c => 2 * idx.get(c >> 1) + (c & 1));
      const exc = x.exc.map(c => 2 * idx.get(c >> 1) + (c & 1));
      lists[h].push({hs: x.hsign, q: 1.0 - x.conf, body: body, exc: exc, normal: x.normal, rank: x.rank});
    }
    const qidx = insts.map(t => idx.get(t[1].id));
    // An application with a body literal outside the reachable literals is
    // present in no world; it is removed before the cycle groups are formed,
    // so that it decides no dependence (memo 4.6).
    const live = new Set();
    for (const c of possible) if (idx.has(c >> 1)) live.add(2 * idx.get(c >> 1) + (c & 1));
    lists = lists.map(l => l.filter(x => allIn(x.body, live)));
    const deps = lists.map(l => {
      const js = [];
      for (const x of l) {
        for (const c of x.body) js.push(c >> 1);
        for (const c of x.exc) js.push(c >> 1);
      }
      return sortedUniqInts(js);
    });
    const mk = l => {
      const anyNormal = l.some(x => x.normal);
      return {all: l, side: [l.filter(x => x.hs === 0), l.filter(x => x.hs !== 0)], anyNormal: anyNormal};
    };
    const byatom = lists.map(l => {
      const a = mk(l);
      a.ord = a.anyNormal ? mk(l.filter(x => !x.normal)) : a;
      return a;
    });
    // build_comps, with the world-independent tests of world() made once
    const inner = new Array(n);
    const comps = [];
    for (const nodes of components(deps, n)) {
      const members = new Set(nodes);
      const outside = sortedUniqInts([].concat(...nodes.map(i => deps[i].filter(j => !members.has(j)))));
      for (const i of nodes) inner[i] = [];
      for (const h of nodes) for (const j of deps[h]) if (members.has(j)) inner[j].push(h);
      const cyclic = nodes.length > 1 || deps[nodes[0]].indexOf(nodes[0]) >= 0;
      const g = {nodes: nodes, outside: outside, cyclic: cyclic, cross: false, hasNorm: false};
      g.cross = cyclic && isCrossSign(nodes, byatom);
      g.hasNorm = nodes.some(i => byatom[i].anyNormal);
      comps.push(g);
    }
    res.components = comps.length;
    const counts = insts.map(() => [0, 0, 0, 0, 0]);
    const acounts = allAtoms ? order.map(() => [0, 0, 0, 0, 0]) : null;
    const state = new Array(n).fill(IGN), u = new Array(n).fill(0.0), v = new Array(n).fill(0.0);
    const stats = [0, 0];
    // splitmix64 in the order of the atom texts: atom i's U and V are the
    // draws 2i+1 and 2i+2 of a world. The state advances by GOLDEN per draw,
    // so a draw is computed only where it can change a state: U for an atom
    // with an uncertain application or applications of both signs, V where a
    // normal default meets the other sign. The other draws are skipped by
    // their offset; every computed value is the one the full stream gives.
    const both = lists.map(l => new Set(l.map(x => x.hs)).size === 2);
    const needu = [], needv = [];
    for (let i = 0; i < n; i++) {
      if (both[i] || lists[i].some(x => x.q > 0)) {
        needu.push([i].concat(halves((BigInt(2 * i + 1) * GOLDEN) & MASK)));
      }
      if (both[i] && lists[i].some(x => x.normal)) {
        needv.push([i].concat(halves((BigInt(2 * i + 2) * GOLDEN) & MASK)));
      }
    }
    const [stepH, stepL] = halves((BigInt(2 * n) * GOLDEN) & MASK);
    let [sH, sL] = halves(BigInt.asUintN(64, BigInt(seed)));
    const progress = typeof o.progress === "function" ? o.progress : null;
    let lastReport = Date.now();
    for (let t = 0; t < samples; t++) {
      for (let k = 0; k < needu.length; k++) {
        const e = needu[k];
        const lo = sL + e[2];
        u[e[0]] = mixUniform((sH + e[1] + (lo > 0xffffffff ? 1 : 0)) >>> 0, lo >>> 0);
      }
      for (let k = 0; k < needv.length; k++) {
        const e = needv[k];
        const lo = sL + e[2];
        v[e[0]] = mixUniform((sH + e[1] + (lo > 0xffffffff ? 1 : 0)) >>> 0, lo >>> 0);
      }
      const lo = sL + stepL;
      sH = (sH + stepH + (lo > 0xffffffff ? 1 : 0)) >>> 0;
      sL = lo >>> 0;
      world(byatom, comps, inner, u, v, state, stats);
      for (let j = 0; j < qidx.length; j++) counts[j][state[qidx[j]]]++;
      if (allAtoms) for (let i = 0; i < n; i++) acounts[i][state[i]]++;
      if (progress && (t & 1023) === 1023) {
        const now = Date.now();
        if (now - lastReport >= 200) { lastReport = now; progress(t + 1); }
      }
    }
    res.longest_sweeps = stats[0];
    res.sweep_cap_hits = stats[1];
    insts.forEach(([text, key, binding], j) => {
      const a = {instance: text, key: [qs ? "-" : "+", key.pred, key.args === null ? null : key.args.map(c => c.out)]};
      if (inp.qvars.length) a.binding = binding;
      Object.assign(a, summary(counts[j], samples, qs === 1));
      res.answers.push(a);
    });
    if (allAtoms) {
      res.atom_values = order.map((a, i) => (rc.has(a.id) ? {atom: a.text, unsupported: rc.get(a.id)} :
        Object.assign({atom: a.text}, summary(acounts[i], samples, false))));
    }
    return res;
  }

  // ---------------------------------------------------------------- exports and the worker

  const api = {mcref: mcref, VERSION: VERSION, TOOL: TOOL, sha256: sha256,
    _internals: {floatRepr: floatRepr, pyRepr: pyRepr, pyJsonDumps: pyJsonDumps, jsonLoads: jsonLoads,
      stripComments: stripComments, mixUniform: mixUniform, hoeffding: hoeffding, PYFLOAT: PYFLOAT}};

  if (typeof module !== "undefined" && module.exports) {
    module.exports = api;
  } else if (typeof self !== "undefined" && typeof window === "undefined" && typeof self.postMessage === "function") {
    self.onmessage = function (ev) {
      const m = ev.data || {};
      if (m.cmd !== "run") return;
      try {
        const result = mcref(m.input, {samples: m.samples, seed: m.seed, maxGround: m.maxGround,
          allAtoms: m.allAtoms, name: m.name, convertedBy: m.convertedBy, conversionOutput: m.conversionOutput,
          progress: n => self.postMessage({progress: n})});
        self.postMessage({done: true, result: result});
      } catch (e) {
        self.postMessage({error: String((e && e.message) || e)});
      }
    };
  } else if (root) {
    root.mcref = api;
  }
})(typeof globalThis !== "undefined" ? globalThis : this);
