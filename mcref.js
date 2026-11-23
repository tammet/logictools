// mcref.js: a JavaScript port of mcref 1.3.1, the reference tool of the
// support semantics of gk: its exact evaluation and its sampling.
//
// The semantics is Doc/support_semantics.md of the gk repository; the tool
// is Doc/mcref.md. The Python tool is published in
// https://github.com/tammet/gkreasoner (folder mcref/). This file ports the
// default command `mcref.py INPUT [--mode auto|exact|sampling]` of these
// Python files:
//
//   mcref.py         sha256 e7489ee3ef14ebcc506099236ec4dd6962ff8880faa7ab7f09a2a6653179ec13
//   mcref_read.py    sha256 6cddd6a4bf0da459eb2944d0b3a15996733841281f75f47796fbb42a2a5f5206
//   mcref_apps.py    sha256 d09fab3251c3593631df4d8ef5aed90041585823fc5f092710dac32b86826243
//   mcref_proofs.py  sha256 1cd62b63a39eab23fda5e2630b648e706d555f8781bf6fae4e68385befd74072
//   mcref_graph.py   sha256 700bfb415412cef811e2569a6f7af2063520cca3027a875e23fc98225d3f97c9
//   mcref_tables.py  sha256 5f465268830d11e8662971eec4aecc8086bfa72315395e67afe8caf9ab145427
//   mcref_exact.py   sha256 03607c422b7b390dab4e70d44c1f06b3ebc9a535c9a1e43067cc5774710b8aa8
//   mcref_texts.py   sha256 42ed23d1615a7885ed389efec63877fb7d4a091d72a265070ec726029e3607b8
//
// What it computes: the input is grounded over its constants; the single
// applications of the ground statements and the applications of the proofs
// of several statements (resolution with dependency lists) are formed; no
// self-support and the rule for a body that can never hold leave
// applications out; the cycle groups are evaluated by the tables, by
// sweeps, by the narrowing or by the clause rule in a cycle, inside the
// exception pass in layers. Exact evaluation evaluates one world per cell
// of the world space and adds the cell's volume to the state of each atom;
// its result is exact up to the rounding of floating-point numbers.
// Sampling evaluates N drawn worlds with the same evaluation of one world.
// Its random numbers are splitmix64, drawn in the order of mcref.py, so the
// same input, seed and number of worlds give the same counts as mcref.py.
// The mode "auto" (the default) uses exact evaluation when the cells are
// at most maxCells and sampling above it, as mcref.py does.
//
// What it leaves out: the test options of mcref.py (--rules 1.1, --cases,
// --backbone fix, --ranks) and its environment switches: the port computes
// the definition only. The functions keep the Python names in camelCase,
// and each block names the Python function it ports.
//
// The port reads JSON-LD-LOGIC text only. mcref.py converts other input
// languages with `gk FILE -writejson -recursive`. A caller of this port runs
// that conversion first (the page runs the gk wasm build) and passes the
// output with the option convertedBy. The port then reads the output exactly
// as mcref.py reads it.
//
// Use in a Web Worker: post {cmd: "run", input, mode, samples, seed,
// maxCells, maxGround, allAtoms, name, convertedBy, conversionOutput}. The
// worker posts {progress, total, unit} messages (unit "cells" or "worlds"),
// and then {done: true, result} or {error}. The result is the object that
// mcref.py prints under "mcref".
//
// Use under node: const {mcref} = require("./mcref.js");
// const result = mcref(text, {allAtoms: true});
//
// Options of mcref(text, options):
//   mode         "auto" (default), "exact" or "sampling"
//   samples      the number of sampled worlds (default 100000)
//   seed         the seed of splitmix64 (default 1)
//   maxCells     the cell limit of exact evaluation (default 300000)
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
//   progress     a function (done, total, unit) called during the evaluation

(function (root) {
  "use strict";

  const VERSION = "1.3.1-js";
  const TOOL = {
    "mcref.py": "e7489ee3ef14ebcc506099236ec4dd6962ff8880faa7ab7f09a2a6653179ec13",
    "mcref_read.py": "6cddd6a4bf0da459eb2944d0b3a15996733841281f75f47796fbb42a2a5f5206",
    "mcref_apps.py": "d09fab3251c3593631df4d8ef5aed90041585823fc5f092710dac32b86826243",
    "mcref_proofs.py": "1cd62b63a39eab23fda5e2630b648e706d555f8781bf6fae4e68385befd74072",
    "mcref_graph.py": "700bfb415412cef811e2569a6f7af2063520cca3027a875e23fc98225d3f97c9",
    "mcref_tables.py": "5f465268830d11e8662971eec4aecc8086bfa72315395e67afe8caf9ab145427",
    "mcref_exact.py": "03607c422b7b390dab4e70d44c1f06b3ebc9a535c9a1e43067cc5774710b8aa8",
    "mcref_texts.py": "42ed23d1615a7885ed389efec63877fb7d4a091d72a265070ec726029e3607b8"
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
      } else {
        out.push(item);
        if (src.convertedBy) CONVERTED.add(item);   // the converter has decided the head
      }
    }
    return out;
  }

  // the statements that came from gk's converter: their head is not read here
  const CONVERTED = new Set();

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

  // the arguments of two literals as written: variables by name, constants
  // by value (one object per typed constant); null (a bare atom) only
  // equals null
  function argsEq(a, b) {
    if (a === null || b === null) return a === b;
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
    return true;
  }

  // read_head: the index of the consequent literal read as the head, or
  // null. Exactly one exception literal must be the opposite of a consequent
  // literal, and of exactly one; compared as written.
  function readHead(lits, blocks, consIdx) {
    let nmatch = 0, found = -1;
    for (const [, e] of blocks) {
      const m = consIdx.filter(i => lits[i][0] !== e[0] && lits[i][1] === e[1] && argsEq(lits[i][2], e[2]));
      if (m.length) {
        nmatch++;
        found = m.length === 1 ? m[0] : -2;
      }
    }
    return (nmatch === 1 && found >= 0) ? found : null;
  }

  // statement_clauses; read: the head may be read from a default (READHEAD)
  function statementClauses(logic, dirhead, read) {
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
    const cls = cnf(nnf(a, false));
    for (const c of cls) {
      const lits = c.filter(e => e.t === "lit").map(plain);
      const blocks = c.filter(e => e.t === "block").map(e => [e.st, plain(e.lit)]);
      let head = lits.length === 1 ? 0 : null;
      if (read && cls.length === 1 && blocks.length && lits.length >= 2) {
        // the consequent is the right side of an implication, else the whole statement
        let consIdx;
        if (a.t === "imp") {
          const cc = cnf(nnf(a.b, false));
          const cons = cc.length === 1 ? cnf(nnf(a.b, false))[0].filter(e => e.t === "lit") : [];
          consIdx = [];
          lits.forEach((l, i) => {
            if (cons.some(e => e.sign === l[0] && e.pred === l[1] && argsEq(e.args, l[2]))) consIdx.push(i);
          });
        } else {
          consIdx = lits.map((l, i) => i);
        }
        const h = readHead(lits, blocks, consIdx);
        if (h !== null) head = h;
      }
      out.push({lits: lits, blocks: blocks, head: head});
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
      const pcs = statementClauses(logic, dirhead, READHEAD && !CONVERTED.has(st));
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
        // B2: two choices of constants are two ground statements, also when
        // they give the same clause
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
      CONVERTED.clear();
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
  // the field interpretation of a sampling run (mcref_texts.py, as mcref.py run() completes it)
  const INTERPRETATION = {
    "semantics": "the support semantics of Doc/support_semantics.md; the reference definitions are in its Section 11",
    "exception pass": "the layers of signed literals; for each layer, lowest first, an evaluation without the applications of that layer and above and without those removed before, and the removal of the applications of the layer whose external exception literal is usable there; then an evaluation of all applications that are not removed, and the restore step, repeated until no application is restored (Doc/support_semantics.md, Section 11.9)",
    "rules with a written head": "a certain rule without exception literals is used in every direction; below confidence 1 or with an exception literal, at its written head only (Doc/support_semantics.md, Section 11.3)",
    "clauses": "one application per literal; one event per uncertain ground statement of several literals",
    "clauses without a written head": "with the proofs of several statements, such a clause takes part in proofs in every direction, also with a confidence or exception literals; a proof that uses it keeps its exception literals as external exceptions and, when it is uncertain, has its event as a premise",
    "no self-support": "an application with head L is left out when one of its body literals cannot be derived without the applications that have head L (exceptions and opposition ignored); one pass, before the applications whose body can never hold are left out (Doc/support_semantics.md, Section 11.4)",
    "blocked-rule repair": "in every evaluation of the exception pass, the applications held out or removed are absent from the whole preparation: no self-support, the rule for a body that can never hold, the concluded literals and the groups are made again on the others; one preparation per set of absent applications (Doc/support_semantics.md, Section 11.9)",
    "clause rule without a result": "when the clause rule in a cycle has no result, an atom of the group with the same state in every evaluation the rule made keeps it, and the others get no value; when the rule stops at a check that cannot be decided, one more evaluation with every listed clause whose check is open or contradicted counted as contradicted comes first (Doc/support_semantics.md, Section 11.8)",
    "head read from a default": "a statement whose consequent has several literals and which has exception literals has the written head L when exactly one exception literal is the opposite of a consequent literal L, and of exactly one; compared as written, before grounding (Doc/support_semantics.md, Section 11.1); for .gkp input gk's converter reads it, for JSON input this reader",
    "not represented": "nothing within the limits of the proof search; a limit is printed as a reading",
    "domain": "the constants of the input",
    "kind of a side": "decided in each world from the applications present in it (Doc/support_semantics.md, Section 5.5)",
    "groups": "a sweep group (no cycle across signs, no exception literal in the group, no normal default for or against an atom of the group, no outside atom without a value) by sweeps, which settle; every other group by the narrowing, ordinary applications first when the group has normal defaults, an atom left open read as ignorance when the group has no cycle across signs and no outside atom without a value (Doc/support_semantics.md, Section 11.7)",
    "no value": "an atom of a cycle across signs left possible but not sure; a group that depends on an atom without a value runs the narrowing with that atom's two literals possible and neither sure, and an atom of it left possible but not sure has no value too (Doc/support_semantics.md, Section 11.7)",
    "rank contexts": "not covered; an input where they can matter is declined",
    "self exception": "an application whose exception literal is its own body literal never applies",
    "proofs of several statements": "every minimal proof (L, G) of several statements, found by resolution on clauses with the set of statements they come from, gives an application: as body every single literal that G and the non-goal clauses imply; as listed clauses the non-goal clauses of several literals, which must not be contradicted in the world; the exception literals of every statement of L; the identities of its uncertain rules, each rule counted once in the strength of a side. A rule with a written head that is uncertain or has an exception takes part only in the proofs of its own head; a normal default takes part too, and a proof with normal defaults of the proved literal is a normal default of the smallest of their ranks. A proof whose application another application makes redundant is dropped. A listed clause inside a cycle is evaluated by the clause rule in a cycle (Doc/support_semantics.md, Sections 11.4 and 11.8)"
  };
  // ---------------------------------------------------------------- Python's repr of atoms and literals
  //
  // mcref sorts literals by their Python repr, for example
  // (0, ('p', (('s', 'a'),))). An atom of a bare string has args None.

  function reprConst(c) {
    return "('" + c.tag + "', " + (c.tag === "s" ? pyStrRepr(c.str) : c.str) + ")";
  }

  function reprAtom(a) {
    if (a.repr === undefined) {
      let r;
      if (a.none) r = "None";
      else if (!a.args.length) r = "()";
      else r = "(" + a.args.map(reprConst).join(", ") + (a.args.length === 1 ? ",)" : ")");
      a.repr = "(" + pyStrRepr(a.pred) + ", " + r + ")";
    }
    return a.repr;
  }

  function reprLit(code) { return "(" + (code & 1) + ", " + reprAtom(atomList[code >> 1]) + ")"; }

  function byRepr(a, b) { return cmpStr(reprLit(a), reprLit(b)); }

  // Python's "%.6g"
  function fmtG6(x) {
    if (x === 0) return "0";
    let e = Math.floor(Math.log10(Math.abs(x)));
    let m = (Math.abs(x) / Math.pow(10, e)).toPrecision(6);
    if (parseFloat(m) >= 10) { e++; m = (Math.abs(x) / Math.pow(10, e)).toPrecision(6); }
    const sign = x < 0 ? "-" : "";
    if (e < -4 || e >= 6) {
      const mm = m.indexOf(".") >= 0 ? m.replace(/0+$/, "").replace(/\.$/, "") : m;
      const ae = Math.abs(e);
      return sign + mm + "e" + (e < 0 ? "-" : "+") + (ae < 10 ? "0" + ae : String(ae));
    }
    let s = Math.abs(x).toPrecision(6);
    if (s.indexOf("e") >= 0) s = Number(s).toString();
    if (s.indexOf(".") >= 0) s = s.replace(/0+$/, "").replace(/\.$/, "");
    return sign + s;
  }

  // ---------------------------------------------------------------- the states and the rule tables (mcref_tables.py)

  const POS = 0, NEG = 1, CON = 2, IGN = 3, UNRES = 4;

  // the parts of the definition: the default command of mcref.py (--rules 8)
  const LIFT_UND = true, B3 = true, READHEAD = true, RULE1 = true, BLOCKED_REPAIR = true, CIRCLE_KEEP = true;
  const CACHE_LIMIT = 50000, PCACHE_LIMIT = 200000;
  const PROOF_RESOLVENTS = 3000000, PROOF_TRIPLES = 300000, PROOF_APPS = 20000;

  let RULE_W = new Map(), RULE_TEXT = new Map(), PCACHE = new Map();
  let CLAUSE_KEYS = new Map(), CLAUSE_LITS = new Map();   // clause key -> clause atom; clause atom id -> literal codes
  let LAST_PROOFS = null;
  let CLAUSE_OF = new Map();      // clause node index -> literal entries (2 * index + POS or NEG)
  let CONCLUDED = new Set();      // entries 2 * index + POS or NEG that some application concludes
  let CIRCLE_LAST = new Set();
  let CIRCLE_CACHE = new Map(), CIRCLE_CACHE_N = 0;
  let CIRCLE_STATS = {groups: new Map(), unresolved_clause: 0, kept: 0};

  function resetRun() {
    RULE_W = new Map(); RULE_TEXT = new Map(); PCACHE = new Map();
    CLAUSE_KEYS = new Map(); CLAUSE_LITS = new Map(); LAST_PROOFS = null;
    CLAUSE_OF = new Map(); CONCLUDED = new Set(); CIRCLE_LAST = new Set();
    CIRCLE_CACHE = new Map(); CIRCLE_CACHE_N = 0;
    CIRCLE_STATS = {groups: new Map(), unresolved_clause: 0, kept: 0};
  }

  // An evaluated application (tuple_of): [sign, 1 - confidence, body, exceptions, normal, rank(, identities)];
  // the body and exception entries are 2 * atom index + POS or NEG; the identities a sorted array of rule
  // identities, present when the input has an application with rule identities.

  // tuple_of
  function tupleOf(x, idx, part4) {
    const body = x.body.map(c => idx.get(c >> 1) * 2 + (c & 1));
    const exc = x.exc.map(c => idx.get(c >> 1) * 2 + (c & 1));
    if (x.cls) for (const k of x.cls) exc.push(idx.get(k.id) * 2 + POS);
    const t = [x.hsign, 1.0 - x.conf, body, exc, x.normal, x.rank];
    if (part4 && (x.ids || x.rid !== null)) t.push(x.ids ? x.ids : [x.rid]);
    return t;
  }

  function termKey(t) { return t.join(","); }

  function subsetSorted(a, b) {   // sorted int arrays: a is a subset of b
    let j = 0;
    for (let i = 0; i < a.length; i++) {
      while (j < b.length && b[j] < a[i]) j++;
      if (j >= b.length || b[j] !== a[i]) return false;
      j++;
    }
    return true;
  }

  // dnf_prob: the probability that some term has all its identities true
  function dnfProb(terms) {
    const uniqT = new Map();
    for (const t of terms) uniqT.set(termKey(t), t);
    const key = Array.from(uniqT.keys()).sort().join("|");
    const hit = PCACHE.get(key);
    if (hit !== undefined) return hit;
    const ts = Array.from(uniqT.values()).sort((a, b) => a.length - b.length || cmpStr(termKey(a), termKey(b)));
    const mins = [];
    for (const t of ts) if (!mins.some(m => subsetSorted(m, t))) mins.push(t);
    let r;
    if (!mins.length) r = 0.0;
    else if (!mins[0].length) r = 1.0;
    else if (mins.length === 1) {
      r = 1.0;
      for (const i of mins[0]) r *= RULE_W.get(i);
    } else {
      const parts = [], seen = new Set();
      for (const t of mins) {
        if (seen.has(t)) continue;
        const part = [t], todo = [t], idsp = new Set(t);
        seen.add(t);
        while (todo.length) {
          todo.pop();
          for (const t2 of mins) {
            if (!seen.has(t2) && t2.some(i => idsp.has(i))) {
              seen.add(t2);
              part.push(t2);
              todo.push(t2);
              for (const i of t2) idsp.add(i);
            }
          }
        }
        parts.push(part);
      }
      if (parts.length > 1) {
        let q = 1.0;
        for (const part of parts) q *= 1.0 - dnfProb(part);
        r = 1.0 - q;
      } else {
        const cnt = new Map();
        for (const t of mins) for (const i of t) cnt.set(i, (cnt.get(i) || 0) + 1);
        let v = null;
        for (const i of Array.from(cnt.keys()).sort((a, b) => a - b)) if (v === null || cnt.get(i) > cnt.get(v)) v = i;
        const c = RULE_W.get(v);
        r = c * dnfProb(mins.map(t => t.filter(i => i !== v))) + (1.0 - c) * dnfProb(mins.filter(t => t.indexOf(v) < 0));
      }
    }
    if (PCACHE.size < PCACHE_LIMIT) PCACHE.set(key, r);
    return r;
  }

  // pool: the support of a side, r6 the product of 1 - confidence of its six-entry applications
  function pool(r6, p7) {
    const seen = new Set();
    let disjoint = true;
    for (const x of p7) {
      if (x[6].some(i => seen.has(i))) { disjoint = false; break; }
      for (const i of x[6]) seen.add(i);
    }
    if (disjoint) {
      let r = r6;
      for (const x of p7) r *= x[1];
      return 1.0 - r;
    }
    const s7 = dnfProb(p7.map(x => x[6]));
    return 1.0 - r6 * (1.0 - s7);
  }

  // support
  function support(present) {
    let r6 = 1.0;
    const p7 = [];
    for (const x of present) {
      if (x.length > 6) p7.push(x);
      else r6 *= x[1];
    }
    return p7.length ? pool(r6, p7) : 1.0 - r6;
  }

  // rows: the table of the state of one atom
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

  // outcome: the state of one atom from the states of the atoms it reads
  function outcome(apps, state, u, v) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0, ordp = 0, ordn = 0, rp = 0, rn = 0, p7 = null, n7 = null;
    for (const x of apps) {
      let ok = true;
      const body = x[2];
      for (let i = 0; i < body.length; i++) if (state[body[i] >> 1] !== (body[i] & 1)) { ok = false; break; }
      if (ok) {
        const exc = x[3];
        for (let i = 0; i < exc.length; i++) if (state[exc[i] >> 1] === (exc[i] & 1)) { ok = false; break; }
      }
      if (!ok) continue;
      if (x[0] === 0) {
        np++;
        if (x.length > 6) (p7 || (p7 = [])).push(x); else ra *= x[1];
        if (x[4]) rp = Math.max(rp, x[5]); else ordp++;
      } else {
        nn++;
        if (x.length > 6) (n7 || (n7 = [])).push(x); else rb *= x[1];
        if (x[4]) rn = Math.max(rn, x[5]); else ordn++;
      }
    }
    return rows(np, nn, ordp, ordn, rp, rn, p7 ? pool(ra, p7) : 1.0 - ra, n7 ? pool(rb, n7) : 1.0 - rb, u, v);
  }

  // outcome_sets_plain: an application present with its body in bset and no exception in eset
  function outcomeSets(apps, u, v, bset, eset) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0, ordp = 0, ordn = 0, rp = 0, rn = 0, p7 = null, n7 = null;
    for (const x of apps) {
      let ok = true;
      for (const l of x[2]) if (!bset.has(l)) { ok = false; break; }
      if (ok) for (const e of x[3]) if (eset.has(e)) { ok = false; break; }
      if (!ok) continue;
      if (x[0] === 0) {
        np++;
        if (x.length > 6) (p7 || (p7 = [])).push(x); else ra *= x[1];
        if (x[4]) rp = Math.max(rp, x[5]); else ordp++;
      } else {
        nn++;
        if (x.length > 6) (n7 || (n7 = [])).push(x); else rb *= x[1];
        if (x[4]) rn = Math.max(rn, x[5]); else ordn++;
      }
    }
    return rows(np, nn, ordp, ordn, rp, rn, p7 ? pool(ra, p7) : 1.0 - ra, n7 ? pool(rb, n7) : 1.0 - rb, u, v);
  }

  // wf_side_usable: sides without normal defaults
  function wfSideUsable(sign, apps, uVal, vVal, bodyOwn, excOwn, bodyOpp, excOpp) {
    let ra = 1.0, rb = 1.0, np = 0, nn = 0, p7 = null, n7 = null;
    for (const x of apps) {
      const hs = x[0];
      const bset = hs === sign ? bodyOwn : bodyOpp, eset = hs === sign ? excOwn : excOpp;
      let ok = true;
      for (const l of x[2]) if (!bset.has(l)) { ok = false; break; }
      if (ok) for (const e of x[3]) if (eset.has(e)) { ok = false; break; }
      if (!ok) continue;
      if (hs === 0) {
        np++;
        if (x.length > 6) (p7 || (p7 = [])).push(x); else ra *= x[1];
      } else {
        nn++;
        if (x.length > 6) (n7 || (n7 = [])).push(x); else rb *= x[1];
      }
    }
    const a = p7 ? pool(ra, p7) : 1.0 - ra;
    const b = n7 ? pool(rb, n7) : 1.0 - rb;
    if (sign === 0) {
      if (!np) return false;
      return !nn ? (uVal < a) : (b <= uVal && uVal < a);
    }
    if (!nn) return false;
    return !np ? (uVal < b) : (a <= uVal && uVal < b);
  }

  function allIn(lits, set) {
    for (const l of lits) if (!set.has(l)) return false;
    return true;
  }

  function anyIn(lits, set) {
    for (const l of lits) if (set.has(l)) return true;
    return false;
  }

  // side_regimes: [present, normal, rank, least support, largest support]
  function sideRegimes(appsSide, bmin, emax, bmax, emin, requireNonemptyMin) {
    const sMin = [], sMax = [];
    for (const x of appsSide) {
      if (!(allIn(x[2], bmax) && !anyIn(x[3], emin))) continue;
      sMax.push(x);
      if (bmin !== null && allIn(x[2], bmin) && !anyIn(x[3], emax)) sMin.push(x);
    }
    const regs = [];
    if (!sMin.length && !requireNonemptyMin) regs.push([false, false, 0, 0.0, 0.0]);
    if (!sMax.length) return regs;
    if (sMax.some(x => x.length > 6)) return sideRegimesP4(sMin, sMax, regs);
    let rSmin = 1.0, minHasOrd = false;
    for (const x of sMin) {
      rSmin *= x[1];
      if (!x[4]) minHasOrd = true;
    }
    const maxOrds = sMax.filter(x => !x[4]);
    const sMinSet = new Set(sMin);
    if (maxOrds.length) {
      let rSmax = 1.0;
      for (const x of sMax) rSmax *= x[1];
      let rOrdMax;
      if (minHasOrd) rOrdMax = rSmin;
      else {
        let m = -Infinity;
        for (const x of maxOrds) if (!sMinSet.has(x) && x[1] > m) m = x[1];
        rOrdMax = rSmin * m;
      }
      regs.push([true, false, 0, 1.0 - rOrdMax, 1.0 - rSmax]);
    }
    if (!minHasOrd) {
      const nMax = sMax.filter(x => x[4]);
      if (nMax.length) {
        let rBase = null;
        for (const x of sMin) if (rBase === null || x[5] > rBase) rBase = x[5];
        const ranks = Array.from(new Set(nMax.filter(x => rBase === null || x[5] >= rBase).map(x => x[5])))
          .sort((a, b) => a - b);
        for (const rk of ranks) {
          let rRkMin = 1.0;
          for (const x of nMax) if (x[5] <= rk) rRkMin *= x[1];
          let rRkMax;
          if (rBase !== null && rk === rBase) rRkMax = rSmin;
          else {
            let m = -Infinity;
            for (const x of nMax) if (x[5] === rk && !sMinSet.has(x) && x[1] > m) m = x[1];
            rRkMax = rSmin * m;
          }
          regs.push([true, true, rk, 1.0 - rRkMax, 1.0 - rRkMin]);
        }
      }
    }
    return regs;
  }

  // side_regimes_p4: sides with rule identities
  function sideRegimesP4(sMin, sMax, regs) {
    const minHasOrd = sMin.some(x => !x[4]);
    const maxOrds = sMax.filter(x => !x[4]);
    const sMinSet = new Set(sMin);
    if (maxOrds.length) {
      let lo;
      if (minHasOrd) lo = support(sMin);
      else {
        lo = Infinity;
        for (const x of maxOrds) if (!sMinSet.has(x)) lo = Math.min(lo, support(sMin.concat([x])));
      }
      regs.push([true, false, 0, lo, support(sMax)]);
    }
    if (!minHasOrd) {
      const nMax = sMax.filter(x => x[4]);
      if (nMax.length) {
        let rBase = null;
        for (const x of sMin) if (rBase === null || x[5] > rBase) rBase = x[5];
        const ranks = Array.from(new Set(nMax.filter(x => rBase === null || x[5] >= rBase).map(x => x[5])))
          .sort((a, b) => a - b);
        for (const rk of ranks) {
          const hi = support(nMax.filter(x => x[5] <= rk));
          let lo;
          if (rBase !== null && rk === rBase) lo = support(sMin);
          else {
            lo = Infinity;
            for (const x of nMax) if (x[5] === rk && !sMinSet.has(x)) lo = Math.min(lo, support(sMin.concat([x])));
          }
          regs.push([true, true, rk, lo, hi]);
        }
      }
    }
    return regs;
  }

  // row_side_holds
  function rowSideHolds(sign, own, aOwn, opp, bOpp, uVal, vVal) {
    const pOwn = own[0], normOwn = own[1], rOwn = own[2];
    const pOpp = opp[0], normOpp = opp[1], rOpp = opp[2];
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

  // ---------------------------------------------------------------- applications (mcref_apps.py, mcref.py orient)
  //
  // An application: {head (atom), hsign, body, exc (literal codes 2 * atom id + sign), conf, normal, rank, kind,
  // crank, rid, ids (a sorted array of rule identities), cls (the clause node atoms of its listed clauses)}.

  function App(head, hsign, body, exc, conf, normal, rank, kind, crank) {
    return {head: head, hsign: hsign, body: body, exc: exc, conf: conf, normal: normal, rank: rank, kind: kind,
      crank: crank, rid: null, ids: null, cls: null};
  }

  // application
  function application(h, body, excs, strength, conf, crank, flat) {
    const head = atomList[h >> 1], sign = h & 1;
    const comp = h ^ 1;
    if (excs.indexOf(comp) >= 0) {
      return App(head, sign, body, excs.filter(e => e !== comp), conf, true, strength.get(comp), "normal default", crank);
    }
    if (excs.length) return App(head, sign, body, excs.slice(), conf, false, 0, "default", crank);
    return App(head, sign, body, [], conf, false, 0, !body.length ? "fact" : (flat ? "classical" : "directed"), 0);
  }

  // app_text
  function appText(x) {
    let t = litText(x.hsign, x.head.pred, x.head.args);
    if (x.body.length) t += " <- " + x.body.map(codeText).join(", ");
    if (x.exc.length) t += " [unless " + x.exc.map(codeText).join(", ") + "]";
    if (x.ids) t += " [rules: " + x.ids.slice().sort((a, b) => a - b).map(r => RULE_TEXT.has(r) ? RULE_TEXT.get(r) : "#" + r).join("; ") + "]";
    if (x.cls) {
      t += " [clauses: " + x.cls.map(k => CLAUSE_LITS.get(k.id).slice().sort(byRepr).map(codeText).join(" ; ")).join("; ") + "]";
    }
    return t;
  }

  function consistentCodes(codes) {
    const s = new Set(codes);
    for (const c of codes) if (s.has(c ^ 1)) return false;
    return true;
  }

  // orient: the applications of the ground statements (PROOFS on, no case proofs)
  function orient(gclauses) {
    RULE_W = new Map(); RULE_TEXT = new Map(); PCACHE = new Map();
    CLAUSE_KEYS = new Map(); CLAUSE_LITS = new Map(); LAST_PROOFS = null;
    const srcOf = new Map(), ridOf = new Map();
    const apps = [], dropped = [];
    let nsrc = 0;
    const keep = (x, si) => {
      const same = x.exc.filter(e => x.body.indexOf(e) >= 0);
      if (same.length) { dropped.push([si, x, same[0]]); return false; }
      apps.push(x);
      return true;
    };
    gclauses.forEach((gc, gi) => {
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
        const x = application(h, body, excs, strength, conf, crank, false);
        if (conf < 1 && (!x.normal || LIFT_UND) && lits.length > 1) {
          x.rid = RULE_W.size;
          RULE_W.set(x.rid, conf);
          RULE_TEXT.set(x.rid, appText(x) + " (" + fmtG6(conf) + ")");
          ridOf.set(gi, x.rid);
        }
        keep(x, si);
        return;
      }
      let extra = [], c2 = conf;
      if (conf < 1) {
        nsrc++;
        const src = atomOf("$src_" + nsrc, []);
        srcOf.set(gi, src);
        apps.push(App(src, 0, [], [], conf, false, 0, "source event", 0));
        extra = [src.id * 2];
        c2 = 1.0;
      }
      for (let i = 0; i < lits.length; i++) {
        const body = uniq(lits.filter((l, j) => j !== i).map(l => l ^ 1).concat(extra));
        keep(application(lits[i], body, excs, strength, c2, crank, true), si);
      }
    });
    const pr = proofApplications(gclauses, apps, srcOf, ridOf);
    LAST_PROOFS = pr[1];
    for (const x of pr[0]) apps.push(x);
    return [apps, dropped];
  }

  // ---------------------------------------------------------------- the proofs of several statements (mcref_proofs.py)

  function popcountBig(b) {
    let n = 0;
    while (b) {
      let w = Number(b & 0xffffffffn);
      b >>= 32n;
      w = w - ((w >>> 1) & 0x55555555);
      w = (w & 0x33333333) + ((w >>> 2) & 0x33333333);
      n += (((w + (w >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
    }
    return n;
  }

  class ProofLimit extends Error {}

  // a binary heap of [popcount, length, count, clause, deps]
  function heapLess(a, b) { return a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2]))); }
  function heapPush(h, x) {
    h.push(x);
    let i = h.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!heapLess(h[i], h[p])) break;
      const t = h[i]; h[i] = h[p]; h[p] = t;
      i = p;
    }
  }
  function heapPop(h) {
    const top = h[0], last = h.pop();
    if (h.length) {
      h[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1, r = l + 1;
        let m = i;
        if (l < h.length && heapLess(h[l], h[m])) m = l;
        if (r < h.length && heapLess(h[r], h[m])) m = r;
        if (m === i) break;
        const t = h[i]; h[i] = h[m]; h[m] = t;
        i = m;
      }
    }
    return top;
  }

  // A clause of the search is a sorted array of literal numbers (2 * atom + sign); deps a BigInt mask.
  class Store {
    constructor(budget) {
      this.trip = [];
      this.bylit = new Map();
      this.bymin = new Map();
      this.empty = [];
      this.alive = 0;
      this.budget = budget;
    }
    subsumed(c, d) {
      for (const t of this.empty) {
        const e = this.trip[t];
        if (e !== null && (e[1] & ~d) === 0n) return true;
      }
      for (const l of c) {
        const ts = this.bymin.get(l);
        if (!ts) continue;
        for (const t of ts) {
          const e = this.trip[t];
          if (e !== null && (e[1] & ~d) === 0n && subsetSorted(e[0], c)) return true;
        }
      }
      return false;
    }
    removeSubsumed(c, d) {
      let cands;
      if (!c.length) cands = this.trip.map((e, i) => i);
      else {
        let best = c[0], bl = (this.bylit.get(c[0]) || []).length;
        for (const l of c) {
          const k = (this.bylit.get(l) || []).length;
          if (k < bl) { best = l; bl = k; }
        }
        cands = (this.bylit.get(best) || []).slice();
      }
      for (const t of cands) {
        const e = this.trip[t];
        if (e !== null && (d & ~e[1]) === 0n && subsetSorted(c, e[0])) {
          this.trip[t] = null;
          this.alive--;
        }
      }
    }
    add(c, d) {
      const t = this.trip.length;
      this.trip.push([c, d]);
      this.alive++;
      if (this.alive > PROOF_TRIPLES) throw new ProofLimit("more than " + PROOF_TRIPLES + " kept triples of the proof search");
      if (!c.length) this.empty.push(t);
      else {
        if (!this.bymin.has(c[0])) this.bymin.set(c[0], []);
        this.bymin.get(c[0]).push(t);
        for (const l of c) {
          if (!this.bylit.has(l)) this.bylit.set(l, []);
          this.bylit.get(l).push(t);
        }
      }
      return t;
    }
    items() { return this.trip.filter(e => e !== null); }
  }

  // saturate: given-clause saturation; a triple whose deps meet dmask is never resolved on frozenAtom
  function saturate(store, passive, frozenAtom, dmask) {
    const heap = [];
    let cnt = 0;
    for (const [c, d] of passive) heapPush(heap, [popcountBig(d), c.length, cnt++, c, d]);
    const budget = store.budget;
    while (heap.length) {
      const [, , , c, d] = heapPop(heap);
      if (store.subsumed(c, d)) continue;
      store.removeSubsumed(c, d);
      const t = store.add(c, d);
      if (!c.length) continue;
      const dirc = dmask && (d & dmask) !== 0n;
      for (const l of c) {
        if (dirc && (l >> 1) === frozenAtom) continue;
        const partners = store.bylit.get(l ^ 1);
        if (!partners) continue;
        for (const t2 of partners.slice()) {
          const e = store.trip[t2];
          if (e === null || t2 === t) continue;
          const c2 = e[0], d2 = e[1];
          if (dmask && (d2 & dmask) !== 0n && (l >> 1) === frozenAtom) continue;
          budget[0]--;
          if (budget[0] < 0) throw new ProofLimit("more than " + PROOF_RESOLVENTS + " resolvents of the proof search");
          const r = [];
          let i = 0, j = 0;
          while (i < c.length || j < c2.length) {
            let x;
            if (j >= c2.length || (i < c.length && c[i] < c2[j])) x = c[i++];
            else if (i >= c.length || c2[j] < c[i]) x = c2[j++];
            else { x = c[i++]; j++; }
            if (x !== l && x !== (l ^ 1)) r.push(x);
          }
          let taut = false;
          for (let k = 0; k + 1 < r.length; k++) if ((r[k] ^ 1) === r[k + 1]) { taut = true; break; }
          if (taut) continue;
          const d3 = d | d2;
          heapPush(heap, [popcountBig(d3), r.length, cnt++, r, d3]);
        }
      }
    }
    return store;
  }

  // find_proofs
  function findProofs(free, directed, noq, extra) {
    const budget = [PROOF_RESOLVENTS];
    const stats = {free_clauses: free.length, directed_rules: directed.length, parts: 0, parts_saturated: 0,
      directed_heads: 0, triples: 0, resolvents: 0, limit: null};
    const sid = new Map();
    for (const [s] of free) if (!sid.has(s)) sid.set(s, sid.size);
    for (const [s] of directed) if (!sid.has(s)) sid.set(s, sid.size);
    const sof = new Map();
    for (const [s, b] of sid) sof.set(b, s);
    const bit = s => 1n << BigInt(sid.get(s));
    const par = new Map();
    const find = a => {
      while ((par.has(a) ? par.get(a) : a) !== a) {
        const p = par.get(a);
        par.set(a, par.has(p) ? par.get(p) : p);
        a = par.get(a);
      }
      return a;
    };
    const union = (a, b) => {
      const ra = find(a), rb = find(b);
      if (ra !== rb) par.set(ra, rb);
    };
    for (const [, c] of free) {
      const ats = Array.from(new Set(c.map(l => l >> 1))).sort((a, b) => a - b);
      for (const a of ats.slice(1)) union(ats[0], a);
    }
    const holders = new Map();
    for (const [, c] of free) for (const l of c) holders.set(l, (holders.get(l) || 0) + 1);
    const dby = new Map();
    for (const [s, h, c] of directed) {
      if (!dby.has(h)) dby.set(h, []);
      dby.get(h).push([s, c]);
      holders.set(h, (holders.get(h) || 0) + 1);
    }
    const cand = [];
    for (const [l, k] of holders) if ((k >= 2 || extra.has(l)) && !noq.has(l)) cand.push(l);
    cand.sort((a, b) => a - b);
    const partof = new Map();
    for (const [s, c] of free) {
      const r = find(c[0] >> 1);
      if (!partof.has(r)) partof.set(r, []);
      partof.get(r).push([s, c]);
    }
    stats.parts = partof.size;
    const stores = new Map();
    const partStore = root => {
      let st = stores.get(root);
      if (!st) {
        st = new Store(budget);
        saturate(st, (partof.get(root) || []).map(([s, c]) => [c, bit(s)]), null, 0n);
        stores.set(root, st);
        stats.parts_saturated++;
      }
      return st;
    };
    let proofs = [];
    try {
      for (const q of cand) {
        const a = q >> 1;
        const roots = new Set([find(a)]);
        if (!dby.has(q)) {
          if (!partof.has(find(a))) continue;
          const st = partStore(find(a));
          for (const [c, d] of st.items()) if (c.indexOf(q) >= 0 && popcountBig(d) > 1) proofs.push([q, c, d]);
          if (proofs.length > PROOF_APPS) throw new ProofLimit("more than " + PROOF_APPS + " proofs of several statements");
          continue;
        }
        stats.directed_heads++;
        for (const [, c] of dby.get(q)) for (const l of c) roots.add(find(l >> 1));
        const st = new Store(budget);
        for (const r of Array.from(roots).sort((x, y) => x - y)) {
          if (partof.has(r)) for (const [c, d] of partStore(r).items()) st.add(c, d);
        }
        let dmask = 0n;
        const pas = [];
        for (const [s, c] of dby.get(q)) {
          const b = bit(s);
          dmask |= b;
          pas.push([c, b]);
        }
        saturate(st, pas, a, dmask);
        for (const [c, d] of st.items()) if (c.indexOf(q) >= 0 && popcountBig(d) > 1) proofs.push([q, c, d]);
        if (proofs.length > PROOF_APPS) throw new ProofLimit("more than " + PROOF_APPS + " proofs of several statements");
      }
    } catch (e) {
      if (!(e instanceof ProofLimit)) throw e;
      stats.limit = e.message;
      proofs = [];
    }
    stats.resolvents = PROOF_RESOLVENTS - budget[0];
    let tri = 0;
    for (const s of stores.values()) tri += s.alive;
    stats.triples = tri;
    const freeTriples = atoms => {
      const out = [];
      const rs = Array.from(new Set(Array.from(atoms).map(x => find(x)))).sort((x, y) => x - y);
      for (const r of rs) {
        if (stores.has(r)) { for (const e of stores.get(r).items()) out.push(e); }
        else if (partof.has(r)) { for (const e of partStore(r).items()) out.push(e); }
      }
      return out;
    };
    const out = proofs.map(([q, c, d]) => {
      const deps = [];
      for (let b = 0; b < sof.size; b++) if ((d >> BigInt(b)) & 1n) deps.push(sof.get(b));
      return [q, c, deps, d];
    });
    return [out, stats, freeTriples, sid];
  }

  // proof_applications: the applications of the proofs of several statements
  function proofApplications(gclauses, apps, srcOf, ridOf) {
    const num = new Map(), litsOf = [];   // atom id -> number; number -> atom
    const ln = code => {
      const a = code >> 1;
      let k = num.get(a);
      if (k === undefined) { k = litsOf.length; num.set(a, k); litsOf.push(a); }
      return 2 * k + (code & 1);
    };
    const lt = n => litsOf[n >> 1] * 2 + (n & 1);   // back to a literal code
    const free = [], drs = [], meta = new Map(), stclause = new Map(), freeExc = new Map();
    let ranksDiffer = 0;
    const sortedNums = xs => Array.from(new Set(xs)).sort((a, b) => a - b);
    gclauses.forEach((gc, si) => {
      const conf = gc[1], lits = gc[2], blocks = gc[3], head = gc[4];
      if (lits.length < 2) return;
      const c = uniq(lits);
      if (!consistentCodes(c)) return;
      const excs = uniq(blocks.map(b => b[1]));
      stclause.set(si, c);
      if (!blocks.length && conf >= 1) {
        free.push([si, sortedNums(c.map(ln))]);
        return;
      }
      if (head === null) {
        const ls = c.map(ln);
        if (conf < 1) ls.push(ln(srcOf.get(si).id * 2 + 1));
        free.push([si, sortedNums(ls)]);
        if (blocks.length) freeExc.set(si, excs);
        return;
      }
      const hl = lits[head];
      const comp = hl ^ 1;
      const bodyLits = lits.filter((l, i) => i !== head).map(l => l ^ 1);
      if (excs.indexOf(comp) >= 0) {
        let nrank = -Infinity;
        for (const [st, l] of blocks) if (l === comp && st > nrank) nrank = st;
        const rest = excs.filter(e => e !== comp);
        if (rest.some(e => bodyLits.indexOf(e) >= 0)) return;   // the self-exception rule: never applies
        drs.push([si, ln(hl), sortedNums(c.map(ln))]);
        meta.set(si, [rest, conf < 1 ? (ridOf.has(si) ? ridOf.get(si) : null) : null, conf, nrank]);
        return;
      }
      if (excs.some(e => bodyLits.indexOf(e) >= 0)) return;   // the self-exception rule: never applies
      drs.push([si, ln(hl), sortedNums(c.map(ln))]);
      meta.set(si, [excs, ridOf.has(si) ? ridOf.get(si) : null, conf, null]);
    });
    const noq = new Set();
    for (const a of Array.from(num.keys())) {
      if (atomList[a].pred.startsWith("$src")) { noq.add(ln(a * 2)); noq.add(ln(a * 2 + 1)); }
    }
    const extra = new Set();
    for (const [si, excs] of freeExc) {
      for (const l of stclause.get(si)) if (excs.indexOf(l ^ 1) >= 0) extra.add(ln(l));
    }
    const fp = findProofs(free, drs, noq, extra);
    const proofs = fp[0], stats = fp[1], freeTriples = fp[2], sid = fp[3];
    stats.proofs = proofs.length;
    stats.applications = [];
    stats.absorbed = 0;
    stats.normal_uncertain_left_out = 0;
    stats.normal_ranks_differ = 0;
    stats.free_with_exceptions = freeExc.size;
    if (stats.limit || !proofs.length) return [[], stats];
    const freec = new Map(free);
    // the absorbers: [body set, exc set, clause keys, ids, [normal, rank]]
    const have = new Map();
    for (const x of apps) {
      if (x.conf < 1 && x.rid === null) continue;
      const hk = x.head.id * 2 + x.hsign;
      if (!have.has(hk)) have.set(hk, []);
      have.get(hk).push({b: new Set(x.body), e: new Set(x.exc), c: new Set(), i: new Set(x.rid === null ? [] : [x.rid]),
        nk: x.normal ? [true, x.rank] : [false, 0]});
    }
    const clauseKey = cl => cl.slice().sort((a, b) => a - b).join(",");
    const cands = new Map();   // head literal code -> Map(key text -> candidate)
    for (const [q, c, deps] of proofs) {
      const Q = lt(q);
      const others = c.filter(l => l !== q);
      const body = new Set(others.map(l => lt(l ^ 1)));
      const goal = deps.filter(si => (freec.has(si) && freec.get(si).indexOf(q) >= 0) || meta.has(si));
      const non = deps.filter(si => goal.indexOf(si) < 0);
      if (non.length) {
        let nmask = 0n;
        for (const si of non) nmask |= 1n << BigInt(sid.get(si));
        const atoms = new Set();
        for (const si of non) for (const l of freec.get(si)) atoms.add(l >> 1);
        let bad = false;
        const os = new Set(others);
        for (const [c2, d2] of freeTriples(atoms)) {
          if ((d2 & ~nmask) !== 0n) continue;
          const rest = c2.filter(l => !os.has(l));
          if (rest.length === 1) {
            const m = rest[0];
            if (m === q || m === (q ^ 1)) { bad = true; break; }
            body.add(lt(m));
          } else if (!rest.length) { bad = true; break; }
        }
        if (bad) continue;
      }
      const exc = new Set(), ids = new Set();
      let conf = 1.0;
      const nranks = new Set();
      for (const si of deps) if (freeExc.has(si)) for (const e of freeExc.get(si)) exc.add(e);
      for (const si of goal) {
        if (meta.has(si)) {
          const [excs, rid, cf, nrank] = meta.get(si);
          for (const e of excs) exc.add(e);
          if (nrank !== null) nranks.add(nrank);
          if (rid !== null) { ids.add(rid); conf *= cf; }
        }
      }
      if (nranks.size > 1) ranksDiffer++;
      let nk = [false, 0];
      if (nranks.size) { let m = Infinity; for (const r of nranks) m = Math.min(m, r); nk = [true, m]; }
      let selfExc = false;
      for (const e of exc) if (body.has(e)) { selfExc = true; break; }
      if (selfExc) continue;
      const cls = new Map();
      for (const si of non) { const cl = stclause.get(si); cls.set(clauseKey(cl), cl); }
      const bodyS = Array.from(body).sort((a, b) => a - b), excS = Array.from(exc).sort((a, b) => a - b);
      const clsS = Array.from(cls.keys()).sort(), idsS = Array.from(ids).sort((a, b) => a - b);
      const key = bodyS.join(",") + "|" + excS.join(",") + "|" + clsS.join(";") + "|" + idsS.join(",") + "|" +
        (nk[0] ? "T" + nk[1] : "F");
      if (!cands.has(Q)) cands.set(Q, new Map());
      cands.get(Q).set(key, {b: new Set(body), e: new Set(exc), cls: cls, i: new Set(ids), nk: nk, conf: conf,
        size: body.size + exc.size + cls.size + ids.size,
        repr: [bodyS.map(reprLit).sort(cmpStr).join(", "), excS.map(reprLit).sort(cmpStr).join(", "),
          clsS.map(k => cls.get(k).map(reprLit).sort(cmpStr).join(", ")).sort(cmpStr).join("; "),
          idsS.join(", "), nk[0] ? "T" + nk[1] : "F"].join(" | ")});
    }
    stats.normal_ranks_differ = ranksDiffer;
    const subset = (a, b) => { for (const x of a) if (!b.has(x)) return false; return true; };
    const subsetMap = (a, b) => { for (const x of a.keys()) if (!b.has(x)) return false; return true; };
    const newApps = [];
    const heads = Array.from(cands.keys()).sort((x, y) => cmpStr("(" + (x & 1) + ", " + reprAtom(atomList[x >> 1]) + ")",
      "(" + (y & 1) + ", " + reprAtom(atomList[y >> 1]) + ")"));
    for (const hq of heads) {
      const keys = cands.get(hq);
      const old = have.get(hq) || [];
      const order = Array.from(keys.values()).sort((x, y) => x.size - y.size || cmpStr(x.repr, y.repr));
      const kept = [];
      for (const k of order) {
        const absorbs = z => subset(z.b, k.b) && subset(z.e, k.e) && subsetMap(z.c, k.cls) && subset(z.i, k.i) &&
          (!z.nk[0] || (z.nk[0] === k.nk[0] && z.nk[1] === k.nk[1]));
        if (old.some(absorbs) || kept.some(absorbs)) { stats.absorbed++; continue; }
        kept.push({b: k.b, e: k.e, c: k.cls, i: k.i, nk: k.nk});
        const x = App(atomList[hq >> 1], hq & 1, Array.from(k.b).sort(byRepr), Array.from(k.e).sort(byRepr), k.conf,
          k.nk[0], k.nk[1], "proof", 0);
        if (k.i.size) x.ids = Array.from(k.i).sort((a, b) => a - b);
        if (k.cls.size) {
          const cl = Array.from(k.cls.values());
          const ck = z => z.map(reprLit).sort(cmpStr);
          cl.sort((a, b) => {
            const ra = ck(a), rb = ck(b);
            for (let i = 0; i < Math.min(ra.length, rb.length); i++) {
              const r = cmpStr(ra[i], rb[i]);
              if (r) return r;
            }
            return ra.length - rb.length;
          });
          x.cls = cl.map(c3 => {
            const k3 = clauseKey(c3);
            let atom = CLAUSE_KEYS.get(k3);
            if (!atom) {
              atom = atomOf("$clause_" + (CLAUSE_KEYS.size + 1), []);
              CLAUSE_KEYS.set(k3, atom);
              CLAUSE_LITS.set(atom.id, c3.slice().sort(byRepr));
            }
            return atom;
          });
        }
        newApps.push(x);
      }
    }
    stats.applications = newApps.map(appText);
    return [newApps, stats];
  }

  // ---------------------------------------------------------------- the passes before any world (mcref_graph.py)

  function byheadOf(byhead, a) { return byhead.get(a.id) || []; }

  // closure: the atoms the start atoms depend on, through bodies, exceptions and listed clauses
  function closure(starts, byhead) {
    const seen = new Set(), todo = starts.slice();
    while (todo.length) {
      const a = todo.pop();
      if (seen.has(a)) continue;
      seen.add(a);
      if (CLAUSE_LITS.has(a.id)) for (const c of CLAUSE_LITS.get(a.id)) { const b = atomList[c >> 1]; if (!seen.has(b)) todo.push(b); }
      for (const x of byheadOf(byhead, a)) {
        for (const c of x.body) { const b = atomList[c >> 1]; if (!seen.has(b)) todo.push(b); }
        for (const c of x.exc) { const b = atomList[c >> 1]; if (!seen.has(b)) todo.push(b); }
        if (x.cls) for (const k of x.cls) if (!seen.has(k)) todo.push(k);
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

  // reachable: the possible literals (codes)
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

  // rule1_filter: no self-support; RULE1_LAST holds the texts of the left-out applications whose body literals
  // are all reachable
  let RULE1_LAST = [];
  function rule1Filter(apps) {
    RULE1_LAST = [];
    if (!RULE1) return apps;
    const allr = reachable(apps);
    const cache = new Map(), keep = [];
    for (const x of apps) {
      if (x.body.length) {
        const lit = x.head.id * 2 + x.hsign;
        if (!cache.has(lit)) cache.set(lit, reachable(apps.filter(y => y.head.id * 2 + y.hsign !== lit)));
        const r = cache.get(lit);
        if (x.body.some(b => !r.has(b))) {
          if (x.body.every(b => allr.has(b))) RULE1_LAST.push(appText(x));
          continue;
        }
      }
      keep.push(x);
    }
    return keep;
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

  // node_deps: the atoms that atom i reads
  function nodeDeps(i, appsI) {
    const d = new Set();
    for (const x of appsI) {
      for (const l of x[2]) d.add(l >> 1);
      for (const l of x[3]) d.add(l >> 1);
    }
    const cl = CLAUSE_OF.get(i);
    if (cl) for (const l of cl) d.add(l >> 1);
    return d;
  }

  function depsOf(byatom, n) {
    const out = [];
    for (let h = 0; h < n; h++) out.push(Array.from(nodeDeps(h, byatom[h])).sort((a, b) => a - b));
    return out;
  }

  // real_exc: the exception entries without the clause nodes
  function realExc(x) {
    if (!CLAUSE_OF.size) return x[3];
    return x[3].filter(e => !CLAUSE_OF.has(e >> 1));
  }

  function makeComp(nodes, deps) {
    const members = new Set(nodes);
    const outside = new Set();
    for (const i of nodes) for (const j of deps[i]) if (!members.has(j)) outside.add(j);
    const inner = new Map();
    for (const i of nodes) inner.set(i, []);
    for (const h of nodes) for (const j of deps[h]) if (members.has(j)) inner.get(j).push(h);
    return [nodes, Array.from(outside).sort((a, b) => a - b), inner,
      nodes.length > 1 || deps[nodes[0]].indexOf(nodes[0]) >= 0];
  }

  // build_comps
  function buildComps(deps, n) {
    return components(deps, n).map(nodes => makeComp(nodes, deps));
  }

  // build_comps_part: the groups of the atoms `part` alone; deps holds the dependencies of every atom
  function buildCompsPart(deps, part) {
    const loc = new Map();
    part.forEach((i, k) => loc.set(i, k));
    const ldeps = part.map(i => sortedUniqInts(deps[i].filter(j => loc.has(j)).map(j => loc.get(j))));
    return components(ldeps, part.length).map(lnodes => makeComp(lnodes.map(k => part[k]).sort((a, b) => a - b), deps));
  }

  // is_cross_sign
  function isCrossSign(nodes, byatom) {
    const members = new Set(nodes);
    const sg = [false, false];
    for (const h of nodes) {
      for (const x of byatom[h]) {
        const hs = x[0];
        let inside = false;
        for (const l of x[2]) {
          if (members.has(l >> 1)) {
            inside = true;
            if ((l & 1) !== hs) return true;
          }
        }
        if (inside) sg[hs] = true;
      }
    }
    return sg[0] && sg[1];
  }

  // reachable_tuples: the reachable entries of evaluated applications
  function reachableTuples(byatom) {
    const possible = new Set(), waiting = new Map(), need = new Map(), todo = [];
    byatom.forEach((xs, h) => {
      xs.forEach((x, k) => {
        const hk = h + ":" + k;
        need.set(hk, x[2].length);
        for (const lit of x[2]) {
          if (!waiting.has(lit)) waiting.set(lit, []);
          waiting.get(lit).push([h, k, hk]);
        }
        if (!x[2].length) todo.push([h, k, hk]);
      });
    });
    while (todo.length) {
      const [h, k] = todo.pop();
      const lit = 2 * h + (byatom[h][k][0] === 0 ? POS : NEG);
      if (possible.has(lit)) continue;
      possible.add(lit);
      for (const w of waiting.get(lit) || []) {
        const r = need.get(w[2]) - 1;
        need.set(w[2], r);
        if (r === 0) todo.push(w);
      }
    }
    return possible;
  }

  // ---------------------------------------------------------------- the clause nodes (mcref.py)

  function setupClauseNodes(idx) {
    CLAUSE_OF = new Map();
    CIRCLE_CACHE = new Map(); CIRCLE_CACHE_N = 0;
    CONCLUDED = new Set();
    for (const [k, lits] of CLAUSE_LITS) {
      if (idx.has(k)) CLAUSE_OF.set(idx.get(k), lits.map(c => idx.get(c >> 1) * 2 + ((c & 1) === 0 ? POS : NEG)));
    }
  }

  function setupConcluded(byatom) {
    CONCLUDED.clear();
    byatom.forEach((xs, h) => { for (const x of xs) CONCLUDED.add(2 * h + (x[0] === 0 ? POS : NEG)); });
  }

  // clause_state
  function clauseState(c, state) {
    let unres = false;
    for (const l of CLAUSE_OF.get(c)) {
      const j = l >> 1, sg = l & 1;
      const st = state[j];
      if (st === CON || st === (sg === POS ? NEG : POS)) continue;
      if (st === UNRES) {
        if (!CONCLUDED.has(2 * j + (sg === POS ? NEG : POS))) return IGN;
        unres = true;
        continue;
      }
      return IGN;
    }
    return unres ? UNRES : POS;
  }

  // ---------------------------------------------------------------- the narrowing (mcref.py)

  function envSurelyUsable(sign, apps, uVal, vVal, X, L, U) {
    if (!apps.some(x => x[4])) return wfSideUsable(sign, apps, uVal, vVal, X, U, U, L);
    const ownApps = apps.filter(x => x[0] === sign);
    if (!ownApps.some(x => allIn(x[2], X) && !anyIn(x[3], U))) return false;
    const oppApps = apps.filter(x => x[0] !== sign);
    const ownRegs = sideRegimes(ownApps, X, U, U, L, false);
    const oppRegs = sideRegimes(oppApps, L, U, U, L, false);
    for (const o of ownRegs) for (const p of oppRegs) if (!rowSideHolds(sign, o, o[3], p, p[4], uVal, vVal)) return false;
    return true;
  }

  function envPossiblyUsable(sign, apps, uVal, vVal, X, L, U) {
    if (!apps.some(x => x[4])) return wfSideUsable(sign, apps, uVal, vVal, X, L, L, U);
    const ownApps = apps.filter(x => x[0] === sign);
    const ownRegs = sideRegimes(ownApps, null, null, X, L, true);
    if (!ownRegs.length) return false;
    const oppApps = apps.filter(x => x[0] !== sign);
    const oppRegs = sideRegimes(oppApps, L, U, U, L, false);
    for (const o of ownRegs) for (const p of oppRegs) if (rowSideHolds(sign, o, o[4], p, p[3], uVal, vVal)) return true;
    return false;
  }

  function wfLfp(sure, active, ext, byatom, u, v, L, U) {
    const X = new Set(ext);
    const f = sure ? envSurelyUsable : envPossiblyUsable;
    for (;;) {
      let added = false;
      for (const i of active) {
        if (!X.has(2 * i) && f(0, byatom.get(i), u[i], v[i], X, L, U)) { X.add(2 * i); added = true; }
        if (!X.has(2 * i + 1) && f(1, byatom.get(i), u[i], v[i], X, L, U)) { X.add(2 * i + 1); added = true; }
      }
      if (!added) return X;
    }
  }

  function setEq(a, b) {
    if (a.size !== b.size) return false;
    for (const x of a) if (!b.has(x)) return false;
    return true;
  }

  // run_narrow_stage; byatomStage is a Map from atom index to its applications
  function runNarrowStage(nodes, extBase, unresLits, locked, byatomStage, u, v) {
    let sweeps = 0;
    for (;;) {
      const ext = new Set(extBase);
      for (const [ki, kst] of locked) {
        if (kst === POS) ext.add(2 * ki);
        else if (kst === NEG) ext.add(2 * ki + 1);
      }
      const active = nodes.filter(i => !locked.has(i));
      const extPoss = new Set(ext);
      for (const l of unresLits) extPoss.add(l);
      let L = new Set(ext);
      let U = new Set(extPoss);
      for (const i of active) { U.add(2 * i); U.add(2 * i + 1); }
      for (;;) {
        sweeps++;
        const nL = wfLfp(true, active, ext, byatomStage, u, v, L, U);
        const nU = wfLfp(false, active, extPoss, byatomStage, u, v, nL, U);
        if (setEq(nL, L) && setEq(nU, U)) break;
        L = nL; U = nU;
      }
      const newConf = active.filter(i => !L.has(2 * i) && !L.has(2 * i + 1) &&
        outcomeSets(byatomStage.get(i), u[i], v[i], U, L) === CON);
      if (!newConf.length) return [L, U, sweeps];
      for (const i of newConf) locked.set(i, CON);
    }
  }

  // narrow_group
  function narrowGroup(nodes, outside, byatom, u, v, state, unresReading, stats) {
    const extBase = new Set(), unresLits = new Set();
    for (const j of outside) {
      if (state[j] === POS) extBase.add(2 * j);
      else if (state[j] === NEG) extBase.add(2 * j + 1);
      else if (state[j] === UNRES) { unresLits.add(2 * j); unresLits.add(2 * j + 1); }
    }
    const locked = new Map();
    let hasNorm = false;
    for (const i of nodes) for (const x of byatom[i]) if (x[4]) hasNorm = true;
    let sw1 = 0;
    if (hasNorm) {
      const byOrd = new Map();
      for (const i of nodes) byOrd.set(i, byatom[i].filter(x => !x[4]));
      const [L1, U1, s1] = runNarrowStage(nodes, extBase, unresLits, locked, byOrd, u, v);
      sw1 = s1;
      for (const i of nodes) {
        if (locked.has(i)) continue;
        if (L1.has(2 * i)) locked.set(i, POS);
        else if (L1.has(2 * i + 1)) locked.set(i, NEG);
        else if (!U1.has(2 * i) && !U1.has(2 * i + 1)) {
          if (outcomeSets(byOrd.get(i), u[i], v[i], L1, U1) === CON) locked.set(i, CON);
        }
      }
    }
    const byAll = new Map();
    for (const i of nodes) byAll.set(i, byatom[i]);
    const [L, U, sw2] = runNarrowStage(nodes, extBase, unresLits, locked, byAll, u, v);
    if (sw1 + sw2 > stats[0]) stats[0] = sw1 + sw2;
    for (const i of nodes) {
      if (locked.has(i)) state[i] = locked.get(i);
      else if (L.has(2 * i)) state[i] = POS;
      else if (L.has(2 * i + 1)) state[i] = NEG;
      else if (!U.has(2 * i) && !U.has(2 * i + 1)) state[i] = outcomeSets(byatom[i], u[i], v[i], L, U);
      else state[i] = unresReading;
    }
  }

  const ONE = 0, SWEEP = 1, NARROW_IGN = 2, NARROW_UNRES = 3;

  class SweepError extends Error {
    constructor(nodes, sweeps) {
      super("a sweep group did not settle");
      this.nodes = nodes;
      this.sweeps = sweeps;
    }
  }

  // group_kinds
  function groupKinds(comps, byatom) {
    const out = [];
    for (const [nodes, outside, inner, cyclic] of comps) {
      let kind;
      if (!cyclic) kind = ONE;
      else if (isCrossSign(nodes, byatom)) kind = NARROW_UNRES;
      else {
        const members = new Set(nodes);
        let excInside = false, normal = false;
        for (const i of nodes) for (const x of byatom[i]) {
          if (x[4]) normal = true;
          for (const e of x[3]) if (members.has(e >> 1)) excInside = true;
        }
        kind = (excInside || normal) ? NARROW_IGN : SWEEP;
      }
      out.push([nodes, outside, inner, kind]);
    }
    return out;
  }

  // sweep_group
  function sweepGroup(nodes, inner, byatom, u, v, state, stats) {
    for (const i of nodes) state[i] = IGN;
    let dirty = nodes, sw = 0;
    const limit = nodes.length + 2;
    for (;;) {
      sw++;
      const changed = [];
      for (const i of dirty) {
        const s = outcome(byatom[i], state, u[i], v[i]);
        if (s !== state[i]) changed.push([i, s]);
      }
      if (!changed.length) break;
      if (sw >= limit) throw new SweepError(nodes, sw);
      const nd = new Set();
      for (const [i, s] of changed) {
        state[i] = s;
        for (const h of inner.get(i)) nd.add(h);
      }
      dirty = Array.from(nd).sort((a, b) => a - b);
    }
    if (sw > stats[0]) stats[0] = sw;
  }

  // eval_group
  function evalGroup(byatom, group, u, v, state, stats) {
    const [nodes, outside, inner, kind] = group;
    if (CLAUSE_OF.size) {
      if (kind === ONE && CLAUSE_OF.has(nodes[0])) {
        state[nodes[0]] = clauseState(nodes[0], state);
        return;
      }
      const cn = nodes.filter(i => CLAUSE_OF.has(i));
      if (cn.length) {
        circleGroup(byatom, group, cn, u, v, state, stats);
        return;
      }
    }
    if (outside.some(j => state[j] === UNRES)) narrowGroup(nodes, outside, byatom, u, v, state, UNRES, stats);
    else if (kind === ONE) {
      const i = nodes[0];
      state[i] = outcome(byatom[i], state, u[i], v[i]);
    } else if (kind === SWEEP) sweepGroup(nodes, inner, byatom, u, v, state, stats);
    else narrowGroup(nodes, outside, byatom, u, v, state, kind === NARROW_IGN ? IGN : UNRES, stats);
  }

  // circle_listed_present
  function circleListedPresent(byatom, nodes, c, state) {
    const members = new Set(nodes);
    for (const h of nodes) {
      for (const x of byatom[h]) {
        if (x[3].indexOf(2 * c + POS) < 0) continue;
        if (x[2].some(l => state[l >> 1] !== (l & 1))) continue;
        if (x[3].some(e => {
          const j = e >> 1;
          return j !== c && !(CLAUSE_OF.has(j) && members.has(j)) && state[j] === (e & 1);
        })) continue;
        return true;
      }
    }
    return false;
  }

  // circle_group: the clause rule in a cycle
  function circleGroup(byatom, group, cn, u, v, state, stats) {
    const nodes = group[0];
    const nkey = nodes.join(",");
    let byMap = CIRCLE_CACHE.get(byatom);
    let ent = byMap ? byMap.get(nkey) : undefined;
    if (ent === undefined) {
      const rest = nodes.filter(i => !CLAUSE_OF.has(i));
      const deps = new Map();
      for (const i of nodes) deps.set(i, Array.from(nodeDeps(i, byatom[i])).sort((a, b) => a - b));
      const depsArr = {};
      for (const [i, d] of deps) depsArr[i] = d;
      const sub = rest.length ? groupKinds(buildCompsPart(depsArr, rest), byatom) : [];
      ent = [rest, sub];
      if (CIRCLE_CACHE_N < CACHE_LIMIT) {
        if (!byMap) { byMap = new Map(); CIRCLE_CACHE.set(byatom, byMap); }
        byMap.set(nkey, ent);
        CIRCLE_CACHE_N++;
      }
    }
    const [rest, sub] = ent;
    let alpha = cn.map(() => IGN);
    let ok = false;
    const hist = [];
    for (let round = 0; round < cn.length + 1; round++) {
      cn.forEach((c, k) => { state[c] = alpha[k]; });
      for (const g of sub) evalGroup(byatom, g, u, v, state, stats);
      hist.push(rest.map(i => state[i]));
      let beta = cn.map(c => clauseState(c, state));
      beta = cn.map((c, k) => (!circleListedPresent(byatom, nodes, c, state) ? alpha[k] : beta[k]));
      if (beta.every((b, k) => b === alpha[k])) {
        ok = true;
        for (const c of cn) state[c] = clauseState(c, state);
        break;
      }
      if (beta.indexOf(UNRES) >= 0) {
        CIRCLE_STATS.unresolved_clause++;
        if (CIRCLE_KEEP) {
          cn.forEach((c, k) => { state[c] = (beta[k] === POS || beta[k] === UNRES) ? POS : IGN; });
          for (const g of sub) evalGroup(byatom, g, u, v, state, stats);
          hist.push(rest.map(i => state[i]));
        }
        break;
      }
      if (alpha.some((a, k) => a === POS && beta[k] !== POS)) break;
      alpha = alpha.map((a, k) => (beta[k] === POS ? POS : a));
    }
    if (!ok) {
      CIRCLE_STATS.groups.set(nkey, nodes);
      if (CIRCLE_KEEP) {
        rest.forEach((i, k) => {
          const first = hist[0][k];
          if (hist.every(h => h[k] === first)) {
            state[i] = first;
            CIRCLE_STATS.kept++;
          } else {
            state[i] = UNRES;
            CIRCLE_LAST.add(i);
          }
        });
        for (const c of cn) {
          state[c] = clauseState(c, state);
          CIRCLE_LAST.add(c);
        }
      } else {
        for (const i of nodes) state[i] = UNRES;
        for (const i of nodes) CIRCLE_LAST.add(i);
      }
    }
  }

  // world_groups
  function worldGroups(byatom, comps, u, v, state, stats) {
    CIRCLE_LAST.clear();
    for (const group of comps) evalGroup(byatom, group, u, v, state, stats);
  }

  // ---------------------------------------------------------------- the exception pass in layers (mcref.py)

  // prepare_available: the applications not in absent, prepared again
  function prepareAvailable(byatom, absent) {
    const n = byatom.length;
    const drop = new Set(absent.map(hk => hk[0] + ":" + hk[1]));
    let keep = [];
    for (let h = 0; h < n; h++) {
      const row = [];
      for (let k = 0; k < byatom[h].length; k++) if (!drop.has(h + ":" + k)) row.push(k);
      keep.push(row);
    }
    if (RULE1) {
      const cache = new Map(), k2 = [];
      for (let h = 0; h < n; h++) {
        const row = [];
        for (const k of keep[h]) {
          const x = byatom[h][k];
          if (x[2].length) {
            const lit = 2 * h + (x[0] === 0 ? POS : NEG);
            if (!cache.has(lit)) {
              const sub = [];
              for (let g = 0; g < n; g++) {
                sub.push(keep[g].filter(j => !(g === h && (byatom[g][j][0] === 0) === ((lit & 1) === POS)))
                  .map(j => byatom[g][j]));
              }
              cache.set(lit, reachableTuples(sub));
            }
            const r = cache.get(lit);
            if (x[2].some(b => !r.has(b))) continue;
          }
          row.push(k);
        }
        k2.push(row);
      }
      keep = k2;
    }
    const poss = reachableTuples(keep.map((ks, h) => ks.map(k => byatom[h][k])));
    keep = keep.map((ks, h) => ks.filter(k => allIn(byatom[h][k][2], poss)));
    const avail = keep.map((ks, h) => ks.map(k => byatom[h][k]));
    const concl = new Set();
    avail.forEach((xs, h) => { for (const x of xs) concl.add(2 * h + (x[0] === 0 ? POS : NEG)); });
    const comps = groupKinds(buildComps(depsOf(avail, n), n), avail);
    return [avail, comps, concl];
  }

  // judge_pass with the blocked-rule repair
  function judgePass(bb, byatom, comps, removed, u, v, state, stats) {
    CIRCLE_LAST.clear();
    if (BLOCKED_REPAIR && removed.length) {
      const key = removed.map(hk => hk[0] + ":" + hk[1]).join(",");
      let ent = bb.rcache.get(key);
      if (ent === undefined) {
        ent = prepareAvailable(byatom, removed);
        if (bb.rcache.size < CACHE_LIMIT) bb.rcache.set(key, ent);
      }
      const [avail, comps2, concl] = ent;
      const saved = CONCLUDED;
      CONCLUDED = concl;
      try {
        for (const group of comps2) evalGroup(avail, group, u, v, state, stats);
      } finally {
        CONCLUDED = saved;
      }
      return;
    }
    for (const group of comps) evalGroup(byatom, group, u, v, state, stats);
  }

  // compute_layers
  function computeLayers(byatom) {
    const n = byatom.length;
    const top = 2 * n + 1;
    const sig = byatom.map(xs => xs.map(x => (realExc(x).length ? 1 : 0)));
    const reads = byatom.map(xs => xs.map(x => {
      const r = x[2].slice();
      for (const e of x[3]) {
        const cl = CLAUSE_OF.get(e >> 1);
        if (cl) for (const l of cl) r.push((l >> 1) * 2 + ((l & 1) === POS ? NEG : POS));
      }
      return r;
    }));
    for (let round = 0; round < top + 1; round++) {
      const lit = new Map();
      const get = k => (lit.has(k) ? lit.get(k) : 0);
      for (let h = 0; h < n; h++) byatom[h].forEach((x, k) => {
        const key = 2 * h + (x[0] === 0 ? POS : NEG);
        lit.set(key, Math.max(get(key), sig[h][k]));
      });
      for (let inner = 0; inner < 2 * n + 1; inner++) {
        let changed = false;
        for (let h = 0; h < n; h++) byatom[h].forEach((x, k) => {
          const key = 2 * h + (x[0] === 0 ? POS : NEG);
          for (const b of reads[h][k]) {
            if (get(b) > get(key)) { lit.set(key, get(b)); changed = true; }
          }
        });
        if (!changed) break;
      }
      let changed = false;
      for (let h = 0; h < n; h++) byatom[h].forEach((x, k) => {
        const ex = realExc(x);
        if (ex.length) {
          let m = 0;
          for (const e of ex) m = Math.max(m, get(e));
          const req = Math.min(top, 1 + m);
          if (req !== sig[h][k]) { sig[h][k] = req; changed = true; }
        }
      });
      if (!changed) break;
    }
    return sig;
  }

  function cmpHK(a, b) { return a[0] - b[0] || a[1] - b[1]; }

  // make_plan: the exception pass in layers (variant judge with LAYERS)
  function makePlan(byatom) {
    const n = byatom.length;
    const bb = {st1: new Array(n).fill(IGN), rcache: new Map(), removed0: [], removed: [], rounds: 0};
    bb.sigma = computeLayers(byatom);
    let maxS = 0;
    for (const row of bb.sigma) for (const x of row) if (x > maxS) maxS = x;
    bb.max_s = maxS;
    bb.by_level = [];
    for (let lev = 0; lev < maxS + 2; lev++) bb.by_level.push([]);
    bb.sigma.forEach((row, h) => row.forEach((lev, k) => { if (lev > 0) bb.by_level[lev].push([h, k]); }));
    bb.by_level_ge = [];
    for (let lev = 1; lev < maxS + 2; lev++) {
      const xs = [];
      for (let l2 = lev; l2 <= maxS; l2++) for (const hk of bb.by_level[l2]) xs.push(hk);
      bb.by_level_ge[lev] = xs.sort(cmpHK);
    }
    return bb;
  }

  // world_layers: one world of the exception pass, exceptions judged in layers
  function world(bb, byatom, comps, u, v, state, stats) {
    const top = bb.max_s;
    let removed = [];
    const why = new Map();
    if (top > 0) {
      const stCur = bb.st1;
      for (let lev = 1; lev <= top; lev++) {
        const hold = new Map();
        for (const hk of removed.concat(bb.by_level_ge[lev])) hold.set(hk[0] + ":" + hk[1], hk);
        const holdS = Array.from(hold.values()).sort(cmpHK);
        stCur.fill(IGN);
        judgePass(bb, byatom, comps, holdS, u, v, stCur, stats);
        for (const [h, k] of bb.by_level[lev]) {
          const est = realExc(byatom[h][k]).filter(e => stCur[e >> 1] === (e & 1));
          if (est.length) {
            removed.push([h, k]);
            why.set(h + ":" + k, est);
          }
        }
      }
    }
    bb.removed0 = removed.slice();
    bb.rounds = 0;
    if (!removed.length) {
      bb.removed = removed;
      worldGroups(byatom, comps, u, v, state, stats);
      return;
    }
    removed = removed.slice().sort(cmpHK);
    for (;;) {
      judgePass(bb, byatom, comps, removed, u, v, state, stats);
      const keep = removed.filter(([h, k]) => why.get(h + ":" + k).some(e => state[e >> 1] === (e & 1)));
      if (keep.length === removed.length) break;
      removed = keep;
      bb.rounds++;
    }
    bb.removed = removed;
  }

  // ---------------------------------------------------------------- exact evaluation (mcref_exact.py)

  // itertools.combinations(xs, k), in index order
  function* combinations(xs, k) {
    const n = xs.length;
    if (k > n) return;
    const ix = [];
    for (let i = 0; i < k; i++) ix.push(i);
    for (;;) {
      yield ix.map(i => xs[i]);
      let i = k - 1;
      while (i >= 0 && ix[i] === i + n - k) i--;
      if (i < 0) return;
      ix[i]++;
      for (let j = i + 1; j < k; j++) ix[j] = ix[j - 1] + 1;
    }
  }

  class CellOverflow extends Error {}

  // cut_points: 0, 1 and the support of every subset of an atom's applications of each sign
  function cutPoints(appsOfAtom) {
    const pts = new Set([0.0, 1.0]);
    for (const sign of [0, 1]) {
      const side = appsOfAtom.filter(x => x[0] === sign);
      const qs = side.map(x => x[1]);
      if (qs.length > 16) throw new CellOverflow("an atom with " + qs.length + " applications of one sign");
      if (side.some(x => x.length > 6)) {
        for (let k = 0; k <= side.length; k++) {
          for (const sub of combinations(side, k)) {
            const a = support(sub);
            if (a > 0.0 && a < 1.0) pts.add(a);
          }
        }
        continue;
      }
      for (let k = 0; k <= qs.length; k++) {
        for (const sub of combinations(qs, k)) {
          let r = 1.0;
          for (const q of sub) r *= q;
          const a = 1.0 - r;
          if (a > 0.0 && a < 1.0) pts.add(a);
        }
      }
    }
    return Array.from(pts).sort((a, b) => a - b);
  }

  // ---------------------------------------------------------------- the run (mcref_exact.py prepare and run)

  const KINDS = ["one", "sweep", "narrow_ign", "narrow_unres"];

  function untyped(c) { return c.out; }

  // prepare: mcref.run() up to the loop over the worlds
  function prepare(inp, allAtoms) {
    const [qs, qp, qargs] = inp.question;
    const [apps0, dropped] = orient(inp.ground);
    let apps = apps0;
    const byhead = new Map();
    for (const x of apps) {
      if (!byhead.has(x.head.id)) byhead.set(x.head.id, []);
      byhead.get(x.head.id).push(x);
    }
    const insts = [];   // [text, atom, binding]
    if (inp.qvars.length) {
      for (const tup of product(inp.constants, inp.qvars.length)) {
        const sub = new Map();
        inp.qvars.forEach((v, k) => sub.set(v, tup[k]));
        const args = qargs.map(a => (typeof a === "string" && sub.has(a)) ? sub.get(a) : a);
        const a = findAtom(qp, args);
        if (a && byhead.has(a.id)) insts.push([litText(qs, qp, args), a, tup.map(untyped)]);
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
    for (const [, k] of insts) atoms.add(k);
    for (const x of apps) if (x.cls) for (const k of x.cls) atoms.add(k);
    for (const lits of CLAUSE_LITS.values()) for (const c of lits) atoms.add(atomList[c >> 1]);
    const qatoms = closure(insts.map(t => t[1]), byhead);
    const rc = rankContexts(atoms, byhead);
    for (const [, k] of insts) if (rc.has(k.id)) return {unsupported: rc.get(k.id)};
    const rel = allAtoms ? atoms : qatoms;
    const readings = [];
    for (const [si, x, lit] of dropped) {
      if (rel.has(x.head)) readings.push(["self exception", "statement " + (si + 1) + ": " + appText(x) +
        " (exception " + codeText(lit) + ")"]);
    }
    apps = rule1Filter(apps);
    const possible = reachable(apps);
    const order = sortAtoms(rel);
    const idx = new Map();
    order.forEach((a, i) => idx.set(a.id, i));
    const n = order.length;
    setupClauseNodes(idx);
    let byatom = [];
    for (let i = 0; i < n; i++) byatom.push([]);
    const part4 = apps.some(x => x.ids);
    for (const x of apps) if (idx.has(x.head.id)) byatom[idx.get(x.head.id)].push(tupleOf(x, idx, part4));
    const live = new Set();
    for (const c of possible) if (idx.has(c >> 1)) live.add(idx.get(c >> 1) * 2 + (c & 1));
    byatom = byatom.map(xs => xs.filter(x => allIn(x[2], live)));
    setupConcluded(byatom);
    const deps = depsOf(byatom, n);
    const comps = groupKinds(buildComps(deps, n), byatom);
    const both = byatom.map(xs => new Set(xs.map(x => x[0])).size === 2);
    const needu = [], needv = [];
    for (let i = 0; i < n; i++) {
      if (both[i] || byatom[i].some(x => x[1] > 0)) needu.push(i);
      if (both[i] && byatom[i].some(x => x[4])) needv.push(i);
    }
    const ps = LAST_PROOFS;
    if (ps !== null) {
      readings.push(["proofs", ps.applications.length + " applications of proofs of several statements (" +
        (ps.proofs || 0) + " proofs, " + (ps.absorbed || 0) + " absorbed)" +
        (ps.limit ? "; LIMIT: " + ps.limit + ", evaluated with the single applications only" : "")]);
    }
    return {inp: inp, insts: insts, order: order, idx: idx, n: n, byatom: byatom, comps: comps, needu: needu,
      needv: needv, readings: readings, rc: rc, qs: qs};
  }

  // mcref(text, options): the command mcref.py INPUT --mode MODE. Mode "auto" (the default): exact evaluation
  // when the cells are at most maxCells, sampling above it; "exact": exact evaluation only; "sampling": sampling
  // only. The output names the method ("mode"), the cells or the worlds, and the error bound.
  function mcref(inputText, options) {
    const o = options || {};
    const mode = o.mode === undefined ? "auto" : o.mode;
    const samples = o.samples === undefined ? 100000 : o.samples;
    const seed = o.seed === undefined ? 1 : o.seed;
    const maxGround = o.maxGround === undefined ? 200000 : o.maxGround;
    if (typeof inputText !== "string") throw new Error("the input must be a text");
    if (mode !== "auto" && mode !== "exact" && mode !== "sampling") throw new Error("mode: auto, exact or sampling");
    if (!Number.isInteger(samples) || samples < 1) throw new Error("samples must be at least 1");
    let res = null, why = null;
    if (mode === "auto" || mode === "exact") {
      const ex = runExact(inputText, o);
      if (ex.too_many_cells && mode === "auto") why = ex.too_many_cells;
      else {
        res = ex;
        res.mode = "exact";
        res.rules = "8";
        res.error_bound = 0.0;
        res.error_bound_text = "exact up to the rounding of floating-point numbers";
      }
    }
    if (res === null) {
      res = runSampling(inputText, o, samples, seed, maxGround, !!o.allAtoms);
      res.mode = "sampling";
      res.rules = "8";
      res.worlds = samples;
      res.error_bound = hoeffding(samples);
      res.error_bound_text = "Hoeffding's inequality with a union bound: 95 per cent for the four shares of one " +
        "answer together";
      if (why) res.exact_not_used = why;
    }
    return res;
  }

  // run of mcref_exact.py: exact evaluation, one world per cell
  function runExact(inputText, o) {
    const maxCells = o.maxCells === undefined ? 300000 : o.maxCells;
    const maxGround = o.maxGround === undefined ? 200000 : o.maxGround;
    const allAtoms = !!o.allAtoms;
    const res = {version: VERSION, input: o.name === undefined ? null : o.name, answers: [], unsupported: null,
      cells: null, too_many_cells: null, evaluated_atoms: null, groups: null};
    const finish = () => res;
    resetTables();
    resetRun();
    let pr;
    try {
      const inp = readInput(inputText, o, maxGround, []);
      pr = prepare(inp, allAtoms);
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
      res.unsupported = e.message;
      return finish();
    }
    if (pr.unsupported) {
      res.unsupported = pr.unsupported;
      return finish();
    }
    const n = pr.n, byatom = pr.byatom, comps = pr.comps;
    res.evaluated_atoms = n;
    res.readings = pr.readings;
    res.groups = comps.filter(g => g[3] !== ONE).map(g => ({atoms: g[0].map(i => pr.order[i].text), kind: KINDS[g[3]]}));
    const axes = [];   // [atom index, 0 for u or 1 for v, bounds]
    try {
      for (const i of pr.needu) axes.push([i, 0, cutPoints(byatom[i])]);
      for (const i of pr.needv) axes.push([i, 1, cutPoints(byatom[i])]);
    } catch (e) {
      if (!(e instanceof CellOverflow)) throw e;
      res.too_many_cells = e.message;
      return finish();
    }
    let big = 1n;   // Python's integers have no size limit
    for (const ax of axes) big *= BigInt(ax[2].length - 1);
    const total = Number(big);
    res.cells = total;
    if (big > BigInt(maxCells)) {
      res.too_many_cells = big.toString() + " cells, more than " + maxCells;
      return finish();
    }
    const qidx = pr.insts.map(t => pr.idx.get(t[1].id));
    const acc = qidx.map(() => [0.0, 0.0, 0.0, 0.0, 0.0]);
    const aacc = allAtoms ? pr.order.map(() => [0.0, 0.0, 0.0, 0.0, 0.0]) : null;
    const state = new Array(n).fill(IGN), u = new Array(n).fill(0.0), v = new Array(n).fill(0.0);
    const stats = [0];
    let circleShare = 0.0;
    const circleQ = qidx.map(() => 0.0);
    CIRCLE_STATS.groups = new Map();
    const bb = makePlan(byatom);
    const m = axes.length;
    const pos = new Array(m).fill(0);
    let done = 0, lastReport = Date.now();
    for (;;) {
      let w = 1.0;
      for (let k = 0; k < m; k++) {
        const b = axes[k][2], lo = b[pos[k]], hi = b[pos[k] + 1];
        const mid = (lo + hi) / 2;
        if (axes[k][1] === 0) u[axes[k][0]] = mid; else v[axes[k][0]] = mid;
        w *= hi - lo;
      }
      try {
        world(bb, byatom, comps, u, v, state, stats);
      } catch (e) {
        if (e instanceof SweepError) {
          throw new Error("mcref " + VERSION + ": internal error: the sweep group {" +
            e.nodes.map(i => pr.order[i].text).join(", ") + "} of " + res.input + " changed a state in sweep " +
            e.sweeps + "; the sweep lemma of Doc/support_semantics.md, Section 12, says that sweep " +
            (e.nodes.length + 2) + " changes nothing");
        }
        throw e;
      }
      if (CIRCLE_LAST.size) {
        circleShare += w;
        qidx.forEach((qi, j) => { if (CIRCLE_LAST.has(qi)) circleQ[j] += w; });
      }
      qidx.forEach((qi, j) => { acc[j][state[qi]] += w; });
      if (allAtoms) for (let i = 0; i < n; i++) aacc[i][state[i]] += w;
      done++;
      if (o.progress && (done & 255) === 0 && Date.now() - lastReport > 500) {
        lastReport = Date.now();
        o.progress(done, total, "cells");
      }
      let k = m - 1;
      while (k >= 0) {
        pos[k]++;
        if (pos[k] < axes[k][2].length - 1) break;
        pos[k] = 0;
        k--;
      }
      if (k < 0) break;
    }
    if (CLAUSE_OF.size) {
      const gs = Array.from(CIRCLE_STATS.groups.values()).sort((a, b) => {
        for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i];
        return a.length - b.length;
      });
      res.clause_rule_in_circle = {world_share: circleShare, question_share: circleQ,
        groups: gs.map(g => g.filter(i => !CLAUSE_OF.has(i)).map(i => pr.order[i].text))};
    }
    if (LAST_PROOFS !== null) {
      const ps = LAST_PROOFS, p = {};
      for (const k of ["limit", "proofs", "absorbed", "triples", "resolvents", "normal_ranks_differ",
        "normal_uncertain_left_out", "free_with_exceptions"]) if (k in ps) p[k] = ps[k];
      p.applications = ps.applications.length;
      res.proofs = p;
    }
    pr.insts.forEach(([text, , binding], j) => {
      const c = acc[j].slice();
      if (pr.qs === 1) { const t = c[0]; c[0] = c[1]; c[1] = t; }
      const a = {instance: text, value: c.slice(0, 4), unstable: c[4]};
      if (pr.inp.qvars.length) a.binding = binding;
      res.answers.push(a);
    });
    if (allAtoms) {
      res.atom_values = [];
      pr.order.forEach((a, i) => {
        if (CLAUSE_OF.has(i)) return;
        res.atom_values.push(pr.rc.has(a.id) ? {atom: a.text, unsupported: pr.rc.get(a.id)} :
          {atom: a.text, value: aacc[i].slice(0, 4), unstable: aacc[i][4]});
      });
    }
    return finish();
  }

  // ---------------------------------------------------------------- sampling (mcref.py run)

  function hoeffding(n) { return n ? Math.sqrt(Math.log(8 / 0.05) / (2 * n)) : 1.0; }

  // summary: the counts of one atom, its four shares, the share without a value and the 95 % intervals
  function summary(counts, n, swap) {
    const c = counts.slice();
    if (swap) { const t = c[0]; c[0] = c[1]; c[1] = t; }
    const e = hoeffding(n);
    const val = c.slice(0, 4).map(x => x / n);
    return {counts: c, value: val, unstable: c[4] / n,
      interval_95: val.map(p => [Math.max(0.0, p - e), Math.min(1.0, p + e)])};
  }

  // splitmix64 with 32-bit halves: mcref.py computes it on Python integers; the values are the same
  const TWO53 = Math.pow(2, -53);
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

  const MASK = (1n << 64n) - 1n;
  const GOLDEN = 0x9E3779B97F4A7C15n;   // splitmix64's increment

  function halves(b) { return [Number(b >> 32n), Number(b & 0xffffffffn)]; }

  // run: sampling, the output of `mcref.py INPUT --mode sampling`
  function runSampling(inputText, o, samples, seed, maxGround, allAtoms) {
    const interp = Object.assign({}, INTERPRETATION);
    const res = {version: VERSION, input: o.name === undefined ? null : o.name, converted_by: null,
      interpretation: interp, question: null, variables: [], constants: null, ground_clauses: null, atoms: null,
      applications: null, evaluated_atoms: null, components: null, samples: samples, seed: seed, readings: [],
      answers: [], backbone: null, cases: null, unsupported: null,
      provenance: {tool: Object.assign({}, TOOL), files: [["input text", sha256(inputText)]]}};
    resetTables();
    resetRun();
    let inp;
    try {
      inp = readInput(inputText, o, maxGround, res.provenance.files);
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
      res.unsupported = e.message;
      res.converted_by = o.convertedBy ? "gk -writejson -recursive" : null;
      return res;
    }
    res.converted_by = inp.convertedBy;
    const [qs, qp, qargs] = inp.question;
    res.question = litText(qs, qp, qargs);
    res.variables = inp.qvars.map(a => a.slice(2));
    res.constants = inp.constants.length;
    res.ground_clauses = inp.ground.length;
    const [apps0, dropped] = orient(inp.ground);
    let apps = apps0;
    const pstats = LAST_PROOFS;
    res.applications = apps.length;
    res.self_exception_applications = dropped.length;
    const byhead = new Map();
    for (const x of apps) {
      if (!byhead.has(x.head.id)) byhead.set(x.head.id, []);
      byhead.get(x.head.id).push(x);
    }
    const insts = [];
    if (inp.qvars.length) {
      for (const tup of product(inp.constants, inp.qvars.length)) {
        const sub = new Map();
        inp.qvars.forEach((v, k) => sub.set(v, tup[k]));
        const args = qargs.map(a => (typeof a === "string" && sub.has(a)) ? sub.get(a) : a);
        const a = findAtom(qp, args);
        if (a && byhead.has(a.id)) insts.push([litText(qs, qp, args), a, tup.map(untyped)]);
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
    for (const [, k] of insts) atoms.add(k);
    for (const x of apps) if (x.cls) for (const k of x.cls) atoms.add(k);
    for (const lits of CLAUSE_LITS.values()) for (const c of lits) atoms.add(atomList[c >> 1]);
    res.atoms = atoms.size;
    const qatoms = closure(insts.map(t => t[1]), byhead);
    const rc = rankContexts(atoms, byhead);
    for (const [, k] of insts) if (rc.has(k.id)) { res.unsupported = rc.get(k.id); return res; }
    const rel = allAtoms ? atoms : qatoms;
    if (pstats !== null) {
      const mine = apps.filter(x => x.kind === "proof" && qatoms.has(x.head)).map(appText);
      res.proofs = {applications: mine, applications_of_input: pstats.applications.length, proofs: pstats.proofs || 0,
        absorbed: pstats.absorbed || 0, free_clauses: pstats.free_clauses, directed_rules: pstats.directed_rules,
        parts_saturated: pstats.parts_saturated, triples: pstats.triples, resolvents: pstats.resolvents,
        limit: pstats.limit, normal_ranks_differ: pstats.normal_ranks_differ || 0,
        normal_uncertain_left_out: pstats.normal_uncertain_left_out || 0,
        free_with_exceptions: pstats.free_with_exceptions || 0};
      if (pstats.limit) {
        res.readings.push(["proofs", "LIMIT: the proofs of several statements are incomplete (" + pstats.limit +
          "); the input was evaluated with the single applications only"]);
        res.proofs_incomplete = pstats.limit;
      } else if (mine.length) {
        res.readings.push(["proofs", "proofs of several statements gave the applications " + mine.join("; ")]);
      }
      if (pstats.normal_ranks_differ) {
        res.readings.push(["proofs", pstats.normal_ranks_differ + " proofs with normal defaults of different ranks " +
          "count as normal defaults of the smallest of their ranks"]);
      }
      if (pstats.normal_uncertain_left_out) {
        res.readings.push(["proofs", pstats.normal_uncertain_left_out + " uncertain normal defaults take no part in " +
          "proofs of several statements (no identity to count them once); their single applications only"]);
      }
    }
    for (const [si, x, lit] of dropped) {
      if (rel.has(x.head)) res.readings.push(["self exception", "statement " + (si + 1) + ": " + appText(x) +
        " (exception " + codeText(lit) + ")"]);
    }
    apps = rule1Filter(apps);
    if (RULE1_LAST.length) res.left_out_by_no_self_support = RULE1_LAST.slice();
    const possible = reachable(apps);
    const order = sortAtoms(rel);
    const idx = new Map();
    order.forEach((a, i) => idx.set(a.id, i));
    const n = order.length;
    res.evaluated_atoms = n;
    setupClauseNodes(idx);
    let byatom = [], appof = [];
    for (let i = 0; i < n; i++) { byatom.push([]); appof.push([]); }
    const part4 = apps.some(x => x.ids);
    for (const x of apps) {
      if (idx.has(x.head.id)) {
        const h = idx.get(x.head.id);
        byatom[h].push(tupleOf(x, idx, part4));
        appof[h].push(x);
      }
    }
    const qidx = insts.map(t => idx.get(t[1].id));
    const live = new Set();
    for (const c of possible) if (idx.has(c >> 1)) live.add(idx.get(c >> 1) * 2 + (c & 1));
    appof = appof.map((xs, h) => xs.filter((a, k) => allIn(byatom[h][k][2], live)));
    byatom = byatom.map(xs => xs.filter(x => allIn(x[2], live)));
    setupConcluded(byatom);
    const deps = depsOf(byatom, n);
    const comps = groupKinds(buildComps(deps, n), byatom);
    res.components = comps.length;
    const counts = insts.map(() => [0, 0, 0, 0, 0]);
    const acounts = allAtoms ? order.map(() => [0, 0, 0, 0, 0]) : null;
    const state = new Array(n).fill(IGN), u = new Array(n).fill(0.0), v = new Array(n).fill(0.0);
    const stats = [0];
    // splitmix64 in the order of the atom texts: atom i's U and V are the draws 2i+1 and 2i+2 of a world; a draw
    // is computed only where it can change a state, and every computed value is the one the full stream gives
    const both = byatom.map(xs => new Set(xs.map(x => x[0])).size === 2);
    const needu = [], needv = [];
    for (let i = 0; i < n; i++) {
      if (both[i] || byatom[i].some(x => x[1] > 0)) needu.push([i].concat(halves((BigInt(2 * i + 1) * GOLDEN) & MASK)));
      if (both[i] && byatom[i].some(x => x[4])) needv.push([i].concat(halves((BigInt(2 * i + 2) * GOLDEN) & MASK)));
    }
    const [stepH, stepL] = halves((BigInt(2 * n) * GOLDEN) & MASK);
    let [sH, sL] = halves(BigInt.asUintN(64, BigInt(seed)));
    const bb = makePlan(byatom);
    const wset = new Set();
    for (let i = 0; i < n; i++) if (qatoms.has(order[i])) wset.add(i);
    let wFixing = 0, wCycle = 0, wReopen = 0, wRestoring = 0, wRound = 0, wMulti = 0, maxRounds = 0, wRestUsable = 0;
    const rcount = new Map(), reopen = new Map(), restc = new Map();
    const cyc = new Array(n).fill(false);
    for (const [nodes, , , kind] of comps) for (const i of nodes) cyc[i] = kind !== ONE;
    let circleWorlds = 0;
    const circleQ = qidx.map(() => 0);
    CIRCLE_STATS.groups = new Map();
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
      try {
        world(bb, byatom, comps, u, v, state, stats);
      } catch (e) {
        if (e instanceof SweepError) {
          throw new Error("mcref " + VERSION + ": internal error: the sweep group {" +
            e.nodes.map(i => order[i].text).join(", ") + "} of " + res.input + " changed a state in sweep " +
            e.sweeps + "; the sweep lemma of Doc/support_semantics.md, Section 12, says that sweep " +
            (e.nodes.length + 2) + " changes nothing");
        }
        throw e;
      }
      if (CIRCLE_LAST.size) {
        circleWorlds++;
        qidx.forEach((qi, j) => { if (CIRCLE_LAST.has(qi)) circleQ[j]++; });
      }
      for (let j = 0; j < qidx.length; j++) counts[j][state[qidx[j]]]++;
      if (allAtoms) for (let i = 0; i < n; i++) acounts[i][state[i]]++;
      if (bb.removed0.length) {
        if (bb.rounds) {
          wRound++;
          if (bb.rounds > 1) wMulti++;
          if (bb.rounds > maxRounds) maxRounds = bb.rounds;
        }
        const fin = new Set(bb.removed.map(hk => hk[0] + ":" + hk[1]));
        const st1 = bb.st1;
        let hit = false, hcyc = false, hre = false, hrest = false, hru = false;
        for (const [h, k] of bb.removed0) {
          if (!wset.has(h)) continue;
          const exc = realExc(byatom[h][k]);
          const key = h + ":" + k;
          if (fin.has(key)) {
            rcount.set(key, (rcount.get(key) || 0) + 1);
            hit = true;
            hcyc = hcyc || cyc[h];
            for (const e of exc) {
              if (st1[e >> 1] === (e & 1) && state[e >> 1] !== (e & 1)) {
                reopen.set(e >> 1, (reopen.get(e >> 1) || 0) + 1);
                hre = true;
              }
            }
          } else {
            restc.set(key, (restc.get(key) || 0) + 1);
            hrest = true;
            hru = hru || exc.some(e => st1[e >> 1] === (e & 1) && state[e >> 1] === (e & 1));
          }
        }
        if (hit) wFixing++;
        if (hcyc) wCycle++;
        if (hre) wReopen++;
        if (hrest) wRestoring++;
        if (hru) wRestUsable++;
      }
      if (progress && (t & 1023) === 1023) {
        const now = Date.now();
        if (now - lastReport >= 200) { lastReport = now; progress(t + 1, samples, "worlds"); }
      }
    }
    res.longest_sweeps = stats[0];
    if (CLAUSE_OF.size) {
      const gs = Array.from(CIRCLE_STATS.groups.values()).sort((a, b) => {
        for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i];
        return a.length - b.length;
      });
      res.clause_rule_in_circle = {worlds: circleWorlds, question_worlds: circleQ,
        groups: gs.map(g => g.map(i => order[i].text))};
      if (circleWorlds) {
        res.readings.push(["clause rule in a circle", "in " + circleWorlds + " of " + samples + " worlds the clause " +
          "rule in a cycle had no result: a listed clause of the group is contradicted only while its own proof " +
          "applies, or a check cannot be decided; there the atoms of the group that change between its " +
          "evaluations have no value: " + gs.map(g => "{" + g.filter(i => !CLAUSE_OF.has(i)).map(i => order[i].text)
          .join(", ") + "}").join("; ")]);
      }
    }
    const byHK = (a, b) => { const x = a[0].split(":").map(Number), y = b[0].split(":").map(Number); return x[0] - y[0] || x[1] - y[1]; };
    const rem = Array.from(rcount).sort(byHK).map(([key, k]) => { const [h, j] = key.split(":").map(Number); return [appText(appof[h][j]), k]; });
    const rst = Array.from(restc).sort(byHK).map(([key, k]) => { const [h, j] = key.split(":").map(Number); return [appText(appof[h][j]), k]; });
    const reo = Array.from(reopen).sort((a, b) => a[0] - b[0]).map(([e, k]) => [order[e].text, k]);
    res.backbone = {variant: "judge", restore: true, removed: rem.map(([t, k]) => ({application: t, worlds: k})),
      worlds_removing: wFixing, worlds_cycle_group: wCycle,
      restored: rst.map(([t, k]) => ({application: t, worlds: k})), worlds_restoring: wRestoring,
      restored_exception_usable_at_end: wRestUsable, restore_rounds_max: maxRounds,
      worlds_with_restore_rounds: wRound, worlds_with_more_than_one_round: wMulti,
      reopened: reo.map(([t, k]) => ({atom: t, worlds: k})), worlds_reopened: wReopen,
      pass2_group_sets: 0, pass2_cache_full: false};
    const inW = ([t, k]) => t + " (in " + k + " of " + samples + " worlds)";
    if (rem.length) res.readings.push(["backbone", "an exception literal of the application was usable, and the " +
      "exception pass removed it: " + rem.map(inW).join(", ")]);
    if (rst.length) res.readings.push(["backbone", "a removed application was restored, its exception not usable " +
      "in the result without it: " + rst.map(inW).join(", ")]);
    if (reo.length) res.readings.push(["backbone", "the evaluation after the removal left the atom of a removing " +
      "exception literal in another state: " + reo.map(inW).join(", ") + "; the application stays removed"]);
    insts.forEach(([text, key, binding], j) => {
      const a = {instance: text, key: [qs ? "-" : "+", key.pred, key.none ? null : key.args.map(untyped)]};
      if (inp.qvars.length) a.binding = binding;
      Object.assign(a, summary(counts[j], samples, qs === 1));
      res.answers.push(a);
    });
    if (allAtoms) {
      res.atom_values = [];
      order.forEach((a, i) => {
        if (CLAUSE_OF.has(i)) return;
        res.atom_values.push(rc.has(a.id) ? {atom: a.text, unsupported: rc.get(a.id)} :
          Object.assign({atom: a.text}, summary(acounts[i], samples, false)));
      });
    }
    return res;
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

  // ---------------------------------------------------------------- exports and the worker

  const api = {mcref: mcref, VERSION: VERSION, TOOL: TOOL, sha256: sha256,
    _internals: {floatRepr: floatRepr, pyRepr: pyRepr, pyJsonDumps: pyJsonDumps, jsonLoads: jsonLoads,
      stripComments: stripComments, fmtG6: fmtG6, PYFLOAT: PYFLOAT, mixUniform: mixUniform,
      hoeffding: hoeffding}};

  if (typeof module !== "undefined" && module.exports) {
    module.exports = api;
  } else if (typeof self !== "undefined" && typeof window === "undefined" && typeof self.postMessage === "function") {
    self.onmessage = function (ev) {
      const m = ev.data || {};
      if (m.cmd !== "run") return;
      try {
        const result = mcref(m.input, {mode: m.mode, samples: m.samples, seed: m.seed, maxCells: m.maxCells,
          maxGround: m.maxGround, allAtoms: m.allAtoms, name: m.name, convertedBy: m.convertedBy,
          conversionOutput: m.conversionOutput,
          progress: (k, total, unit) => self.postMessage({progress: k, total: total, unit: unit})});
        self.postMessage({done: true, result: result});
      } catch (e) {
        self.postMessage({error: String((e && e.message) || e)});
      }
    };
  } else if (root) {
    root.mcref = api;
  }
})(typeof globalThis !== "undefined" ? globalThis : this);
