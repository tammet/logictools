// gkproofs.js: the proofs of gk's {"recursive": ...} line (gk 1.2.5 and
// later) as text, for commonsense.html.
//
// gk writes each proof with JSON clauses: [n, label, clause] steps, as its
// direct method does. This file prints them in gk's Prolog-like notation
// (GKP), numbered, with a header per proof ("for #1, proof of L, confidence
// c:"); with -fullproof the subproofs stand under the step whose search found
// them, two blanks deeper. It also turns a literal of the line into the text
// form of gk 1.2.4 ("flies(tweety)"), which the page uses to match answers.
//
// The functions follow gk's printer (Printer/dbotterprint.c of gk) and the
// renderer that produced the proof memo of gk 1.2.5; a node check compares
// the two on the page's examples. Numbers print as Python's "%g" prints them.

(function (root) {
  "use strict";

  // functor -> [operator, arity, is a comparison]
  var INFIX = {
    "$sum": ["+", 2, false], "$difference": ["-", 2, false], "$product": ["*", 2, false],
    "$quotient": ["/", 2, false], "$remainder": ["mod", 2, false], "$uminus": ["-", 1, false],
    "$less": ["<", 2, true], "$greater": [">", 2, true], "$lesseq": ["=<", 2, true],
    "$greatereq": [">=", 2, true], "+": ["+", 2, false], "-": ["-", 2, false],
    "*": ["*", 2, false], "/": ["/", 2, false], "<": ["<", 2, true], "=": ["=", 2, true],
    "!=": ["!=", 2, true]
  };

  function infix(f) {
    return (typeof f === "string" && Object.prototype.hasOwnProperty.call(INFIX, f)) ? INFIX[f] : null;
  }

  function isInt(x) { return typeof x === "number" && Number.isInteger(x); }

  // ---- numbers as Python prints them

  // round(x, nd) of Python: the nearest value with nd decimals, a tie to the
  // even last digit; the tie is decided on the exact value of x
  function pyRound(x, nd) {
    if (typeof x !== "number" || !isFinite(x) || Math.abs(x) >= 1e21) return x;
    var exact = Math.abs(x).toFixed(100);
    var dot = exact.indexOf(".");
    var tail = exact.slice(dot + 1 + nd);
    if (/^50*$/.test(tail)) {
      var head = exact.slice(0, dot + 1 + nd);
      var last = head.charCodeAt(head.length - 1) - 48;
      var down = Number(head);
      var r = (last % 2 === 0) ? down : Number(Math.abs(x).toFixed(nd));
      return x < 0 ? -r : r;
    }
    return Number(x.toFixed(nd));
  }

  // "%.<prec>g" of Python: prec significant digits, no trailing zeros, an
  // exponent below 1e-4 and from 10^prec on
  function pyGp(x, prec) {
    if (typeof x !== "number") return String(x);
    if (x === 0) return (1 / x < 0) ? "-0" : "0";
    if (!isFinite(x)) return isNaN(x) ? "nan" : (x > 0 ? "inf" : "-inf");
    var e = x.toExponential(prec - 1).split("e");
    var exp = parseInt(e[1], 10);
    if (exp < -4 || exp >= prec) {
      var mant = e[0].indexOf(".") >= 0 ? e[0].replace(/0+$/, "").replace(/\.$/, "") : e[0];
      var a = Math.abs(exp);
      return mant + "e" + (exp < 0 ? "-" : "+") + (a < 10 ? "0" + a : "" + a);
    }
    var s = x.toFixed(prec - 1 - exp);
    if (s.indexOf(".") >= 0) s = s.replace(/0+$/, "").replace(/\.$/, "");
    return s;
  }

  function pyG(x) { return pyGp(x, 6); }

  function num(x) { return pyG(pyRound(x, 4)); }

  // ---- terms and clauses in GKP

  function shouldQuote(s) {
    if (s.length === 1 && "=-+*/><".indexOf(s) >= 0) return false;
    for (var i = 0; i < s.length; i++) {
      var c = s[i];
      if (c === "$" || c === "_") continue;
      var o = s.charCodeAt(i);
      if (o < 48 || (o > 57 && o < 64) || (o > 90 && o < 97) || o > 122) return true;
    }
    return false;
  }

  function simple(x) {
    if (typeof x === "boolean") return x ? "true" : "false";
    if (typeof x === "number") return isInt(x) ? String(x) : x.toFixed(6);
    if (x === null || x === undefined) return String(x);
    x = String(x);
    if (x.indexOf("?:") === 0) {
      var v = x.slice(2);
      return /^[0-9]+$/.test(v) ? "X" + v : v;   // gk's text names variable 2006 X2006
    }
    if (x.indexOf("#:") === 0) return '"' + x.slice(2).replace(/"/g, '\\"') + '"';
    if (x === "") return "''";
    if (x.indexOf("'") >= 0) return "'" + x.replace(/'/g, "\\'") + "'";
    if (shouldQuote(x)) return "'" + x + "'";
    return x;
  }

  function prefix(t) {
    var argnested = infix(t[0]) !== null;
    var a = [];
    for (var i = 1; i < t.length; i++) a.push(term(t[i], argnested));
    return simple(t[0]) + "(" + a.join(",") + ")";
  }

  function term(t, nested) {
    if (!Array.isArray(t)) return simple(t);
    var op = infix(t[0]);
    if (!op || op[1] !== t.length - 1 || (op[2] && nested)) return prefix(t);
    var s;
    if (op[1] === 1) {
      s = "-(" + term(t[1]) + ")";
      return nested ? "(" + s + ")" : s;
    }
    var left = term(t[1], !op[2]);
    if (op[2] && Array.isArray(t[1]) && (left[0] === "(" || left[0] === "-")) left = prefix(t[1]);
    s = left + " " + op[0] + " " + term(t[2], !op[2]);
    return nested ? "(" + s + ")" : s;
  }

  function isBlock(l) { return Array.isArray(l) && l.length > 0 && l[0] === "$block"; }

  // [is negative, atom] of a literal
  function negAtom(l) {
    if (Array.isArray(l)) {
      var f = l[0];
      if (typeof f === "string" && f.length > 1 && f[0] === "-") return [true, [f.slice(1)].concat(l.slice(1))];
      return [false, l];
    }
    if (typeof l === "string" && l.length > 1 && l[0] === "-") return [true, l.slice(1)];
    return [false, l];
  }

  function isComparison(atom) {
    if (!Array.isArray(atom)) return false;
    var op = infix(atom[0]);
    return !!(op && op[2] && op[1] === atom.length - 1);
  }

  function blocker(l) {
    var strength = l[1], cond = l[2], c;
    if (Array.isArray(cond) && cond.length >= 2 && cond[0] === "$not") c = "-" + term(cond[1]);
    else {
      var na = negAtom(cond);
      c = (na[0] ? "-" : "") + term(na[1]);
    }
    var s = "unless(" + c;
    if (Array.isArray(strength) && strength.length >= 2 && strength[0] === "$")
      s += ", tax(" + simple(strength[1]) + (strength.length >= 3 ? ", " + simple(strength[2]) : "") + ")";
    else if (Array.isArray(strength)) s += ", " + term(strength);
    else if (!(isInt(strength) && strength === 0) && strength !== false) s += ", " + simple(strength);
    return s + ")";
  }

  function same(a, b) { return JSON.stringify(a) === JSON.stringify(b); }

  // the literals of a clause as [is a guard, is negative, atom]
  function lits(cl) {
    return cl.map(function (l) {
      if (isBlock(l)) return [true, false, l];
      var na = negAtom(l);
      return [false, na[0], na[1]];
    });
  }

  // the positive guard contents of a clause, in order
  function guardAtoms(ls) {
    var out = [];
    ls.forEach(function (x) {
      if (!x[0]) return;
      var a = x[2];
      var cond = (Array.isArray(a) && a.length >= 3) ? a[2] : null;
      if (Array.isArray(cond) && cond.length && cond[0] === "$not") return;
      var na = negAtom(cond);
      if (na[0]) return;
      out.push(na[1]);
    });
    return out;
  }

  // the index of the literal printed as the head, or -1 for the usual rule:
  // the written head that gk marks on an input step ({"head": k}); for a
  // derived clause without a positive literal, the negative literal whose
  // atom is the content of one of its guards (gk 1.2.5)
  function writtenHead(cl, head, derived) {
    if (!Array.isArray(cl)) return -1;
    if (head !== null && head !== undefined) return head;
    if (!derived) return -1;
    var ls = lits(cl);
    for (var i = 0; i < ls.length; i++) if (!ls[i][0] && !ls[i][1]) return -1;
    var ga = guardAtoms(ls);
    for (var g = 0; g < ga.length; g++)
      for (var j = 0; j < ls.length; j++)
        if (!ls[j][0] && ls[j][1] && !isComparison(ls[j][2]) && same(ls[j][2], ga[g])) return j;
    return -1;
  }

  function clause(cl, head, derived) {
    if (cl === false || cl === "false" || (Array.isArray(cl) && cl.length === 0)) return "false";
    if (!Array.isArray(cl)) return String(cl);
    var ls = lits(cl), body = [], i;
    var wh = writtenHead(cl, head, derived);
    if (wh >= 0 && wh < ls.length) {
      var h = ls[wh];
      var out1 = (h[1] ? "-" : "") + term(h[2]);
      for (i = 0; i < ls.length; i++)
        if (!ls[i][0] && i !== wh) body.push((ls[i][1] ? "" : "-") + term(ls[i][2]));
      for (i = 0; i < ls.length; i++) if (ls[i][0]) body.push(blocker(ls[i][2]));
      return out1 + (body.length ? " :- " + body.join(", ") : "");
    }
    var npos = 0, neghead = -1, heads = [];
    for (i = 0; i < ls.length; i++) if (!ls[i][0] && !ls[i][1]) npos++;
    if (!npos)
      for (i = 0; i < ls.length; i++)
        if (!ls[i][0] && ls[i][1] && !isComparison(ls[i][2])) { neghead = i; break; }
    for (i = 0; i < ls.length; i++) if (!ls[i][0] && !ls[i][1]) heads.push(term(ls[i][2]));
    var out = heads.join(" ; "), nheads = heads.length;
    if (neghead >= 0) { out += "-" + term(ls[neghead][2]); nheads++; }
    for (i = 0; i < ls.length; i++)
      if (!ls[i][0] && ls[i][1] && i !== neghead) body.push(term(ls[i][2]));
    for (i = 0; i < ls.length; i++) if (ls[i][0]) body.push(blocker(ls[i][2]));
    if (body.length) out += (nheads ? " :- " : ":- ") + body.join(", ");
    if (!nheads && !body.length) return "false";
    return out;
  }

  // a literal in gk's JSON form as GKP text: ["-flies","pingu"] -> -flies(pingu)
  function literal(l) {
    if (l === null || l === undefined) return "none";
    if (typeof l === "string") return l;
    var na = negAtom(l);
    return (na[0] ? "-" : "") + term(na[1]);
  }

  function lit(x) { return Array.isArray(x) ? literal(x) : String(x); }

  // ---- a literal as the text of gk 1.2.4 (experiments/scripts/gk_line.py)

  // a float as gk's collector prints it (col_dbl_text): the shortest "%g"
  // that reads back as the same number, with ".0" when it has no point
  function numText(x) {
    var s = String(x);
    for (var p = 1; p <= 17; p++) {
      s = pyGp(x, p);
      if (Number(s) === x) break;
    }
    if (!/[.eni]/.test(s)) s += ".0";
    return s;
  }

  function termText(t) {
    if (typeof t === "boolean") return t ? "true" : "false";
    if (typeof t === "number") return isInt(t) ? String(t) : numText(t);
    if (typeof t === "string") {
      if (t.indexOf("?:X") === 0) return "_V" + t.slice(3);
      if (t[0] === ":") return t.slice(1);
      return t;
    }
    if (Array.isArray(t) && t.length) {
      if (t.length === 1) return termText(t[0]);
      return termText(t[0]) + "(" + t.slice(1).map(termText).join(",") + ")";
    }
    return String(t);
  }

  // a question or answer of the line as text; a text (gk 1.2.4 and earlier)
  // and null stay as they are
  function litText(x) {
    return (x === null || x === undefined || typeof x === "string") ? x : termText(x);
  }

  // ---- the proofs

  var LISTNAME = { "for": "for", "against": "against", "guards": "guard" };

  function isRef(x) {
    if (isInt(x)) return true;
    if (!Array.isArray(x) || x.length < 2 || !isInt(x[0])) return false;
    for (var i = 0; i < x.length; i++) if (!(isInt(x[i]) || typeof x[i] === "string")) return false;
    return true;
  }

  function ref(x) { return Array.isArray(x) ? x.map(String).join(".") : String(x); }

  function label(how) {
    var lab;
    if (how[0] === "in") {
      var name = how[1] === "taskgoal" ? "task" : how[1];
      lab = (how.length > 2 && how[2] === "goal" ? "goal(" : "in(") + name + ")";
      return how.length > 3 ? lab + " " + pyG(how[3]) + ":" : lab + ":";
    }
    var n = how.length;
    var tail = n > 2 && typeof how[n - 1] === "number" && typeof how[n - 2] === "string";
    var conf = tail ? how[n - 1] : null;
    var args = tail ? how.slice(1, n - 2) : how.slice(1);
    lab = how[0] + "(" + args.filter(isRef).map(ref).join(", ") + ")";
    return conf !== null ? lab + " " + pyG(conf) + ":" : lab + ":";
  }

  function stepText(st) {
    var how = st[1], cl = st[2];
    var head = (st.length > 3 && st[3] && typeof st[3] === "object" && !Array.isArray(st[3])) ? st[3].head : null;
    return typeof cl === "string" ? cl : clause(cl, head, how[0] !== "in");
  }

  function padRight(s, w) { while (s.length < w) s += " "; return s; }

  function blanks(n) { var s = ""; for (var i = 0; i < n; i++) s += "  "; return s; }

  // one proof: its header and its numbered steps, each followed by the
  // subproofs that the step's searches found (with -fullproof); listname and
  // nr for a listed proof ("for #1, proof of L"), none for a subproof
  function show(p, ind, out, listname, nr) {
    var pad = blanks(ind);
    if (p.listed_as) {
      out.push(pad + "proof of " + lit(p.proves) + ": listed as " +
               (LISTNAME[p.listed_as[0]] || p.listed_as[0]) + " #" + p.listed_as[1]);
      return;
    }
    var pre = listname ? LISTNAME[listname] + " #" + nr + ", " : "";
    var head;
    if (p.proves !== undefined) {
      head = pre + "proof of " + lit(p.proves) + ", confidence " + num(p.confidence);
      if (p.search !== undefined) head += ", found by the search for " + lit(p.search);
    } else {
      head = pre + "proof found by the search for " + lit(p.search) + ", confidence " + num(p.confidence);
    }
    if (p.in_value === false) head += ", not used in the value";
    if (p.guard_of && p.guard_of.length)
      head += " (guard in " + p.guard_of.map(function (g) {
        return (LISTNAME[g[0]] || g[0]) + " #" + g[1]; }).join(", ") + ")";
    if (p.no_new_instances) head += " (no input instance beyond the proof above)";
    out.push(pad + head + ":");
    var subs = p.subproofs || [];
    (p.steps || []).forEach(function (st) {
      out.push(pad + "  " + st[0] + ". " + padRight(label(st[1]), 20) + " " + stepText(st));
      subs.forEach(function (q) { if (q.step === st[0]) show(q, ind + 2, out); });
    });
  }

  // the proofs of one answer as lines of text (an empty list for none)
  function answerProofLines(proof, ind) {
    var out = [];
    if (!proof) return out;
    ["for", "against", "guards"].forEach(function (side) {
      (proof[side] || []).forEach(function (p, k) { show(p, ind || 0, out, side, k + 1); });
    });
    return out;
  }

  // the answers of a line: the answers of a question with variables, or the
  // question itself
  function items(line) {
    if (line.answers !== undefined && line.answers !== null) return line.answers;
    return [{ answer: line.question, value: line.value, signed_confidence: line.signed_confidence,
              proof: line.proof }];
  }

  // the whole line as text, as the proof memo of gk 1.2.5 prints it
  function lineText(line) {
    var out = [];
    items(line).forEach(function (a) {
      var v = a.value, sc = a.signed_confidence;
      out.push("answer " + lit(a.answer) + ", " +
               (sc !== undefined && sc !== null ? "signed confidence " + num(sc) : "no value"));
      if (v) out.push("  value: for " + num(v[0]) + ", against " + num(v[1]) + ", conflict " +
                      num(v[2]) + ", ignorance " + num(v[3]));
      var pr = a.proof;
      answerProofLines(pr, 1).forEach(function (l) { out.push(l); });
      if (!pr || !Object.keys(pr).length) out.push("  (no proof)");
      out.push("");
    });
    return out.join("\n").replace(/\s+$/, "") + "\n";
  }

  var api = { clause: clause, literal: literal, litText: litText, label: label,
              answerProofLines: answerProofLines, lineText: lineText, num: num, pyG: pyG,
              pyRound: pyRound };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  root.GkProofs = api;
})(typeof self !== "undefined" ? self : this);
