// Web Worker for the sampling check ("Monte Carlo") on commonsense.html.
//
// Two independent estimates of GK's reported confidence values:
//
//   clause-activation sampling -- an input weight is read as the activation
//     probability of a ground clause. Each sampled world activates or drops
//     every uncertain ground clause independently; an unweighted proof search
//     (gk -nonegative -plain) then decides the world. Reported as the
//     frequency of provability, optionally minus the frequency in which the
//     answer's negation is provable (gk's own pos-neg functional).
//
//   shared-threshold sampling -- the four components support_for /
//     support_against / conflict / ignorance. Each ground atom draws two
//     independent thresholds; evidence counts only when its aggregated
//     strength clears a threshold. Ordinary positive and negative support for
//     one atom face one shared threshold (GK's opposition resolution). A
//     default and support for its exception condition use both thresholds.
//     This mode runs no proof search.
//
// This is a port of the reference implementation in the gkreasoner
// repository: montecarlo/gkmc.py (clause activation) and
// montecarlo/threshold_worlds.py (shared threshold). Each block below names
// the Python function it ports. The
// semantics are the Python ones; where the browser pipeline has to differ,
// the comment says so. The documented differences are:
//
//   * clauses and input weights come from gk's versioned clause export
//     (-defworlds -clausify -outformat json) instead of from a re-parse of
//     the input file, so any input syntax the page accepts can be sampled
//     and no parser is duplicated here;
//   * the export's weights are post-root-split (a statement splitting
//     into k clauses carries the split values, whose product is the stated
//     weight), where gkmc.py reuses the unsplit statement weight for
//     every clause and warns about it;
//   * shared-threshold mode scores one closed query. The reference runner also
//     evaluates an OPEN query, one closed instance at a time over the named
//     constants; the page's shared-threshold panel shows a single table, so an
//     open query is reported as unsupported here instead.
//
// One module instance decides many worlds: gk frees its database when main
// returns, and repeated callMain with IDENTICAL flags is safe. gk does not
// reset all option globals between calls, so the order inside one instance
// is fixed: reference run, then clause export, then world runs only.

'use strict';

// ---- environment adapter -------------------------------------------------
// In the browser this file is a Web Worker and loads the emscripten glue with
// importScripts. The node verification harness (mc_check.js) cannot use that
// path -- the node build of the glue ignores a preset print handler -- so it
// installs self.MC_HOST with the same two operations before loading this
// file. Everything below the adapter is shared by both.

var HOST = (typeof self !== "undefined" && self.MC_HOST) ? self.MC_HOST : null;

var gkout = "";
var gkReady = false;
var gkLoading = false;
var gkWaiting = [];
var moduleDead = false;       // the solver aborted; this worker must be replaced

// the browser caches the solver files like any other file: both are fetched
// under the build version, so a cached older pair is not paired with this
// worker (the node harness goes through HOST and never uses this Module)
var GK_BUILD = "1.0.6";

var Module = {
  noInitialRun: true,
  locateFile: function (p) { return p + "?v=" + GK_BUILD; },
  print: function (s) { gkout += s + "\n"; },
  printErr: function (s) { /* wasm diagnostics are not part of the answer */ },
  onAbort: function (what) { moduleDead = true; },
  onRuntimeInitialized: function () {
    gkReady = true;
    var q = gkWaiting; gkWaiting = [];
    for (var i = 0; i < q.length; i++) q[i]();
  }
};

// Load the solver if needed, then call cb().
function gkEnsure(cb) {
  if (HOST) { HOST.init(cb); return; }
  if (gkReady) { cb(); return; }
  gkWaiting.push(cb);
  if (!gkLoading) { gkLoading = true; importScripts("gkjs.js?v=" + GK_BUILD); }
}

// Write the given files into the in-memory filesystem, run gk with args,
// return everything it printed.
function gkRun(files, args) {
  if (HOST) return HOST.run(files, args);
  for (var i = 0; i < files.length; i++)
    Module.FS.writeFile(files[i].name, files[i].data);
  gkout = "";
  try { Module.callMain(args); }
  catch (e) { /* emscripten exit() throws ExitStatus; normal */ }
  return gkout;
}

function post(msg) {
  if (typeof self !== "undefined" && typeof self.postMessage === "function")
    self.postMessage(msg);
}

// ---- unsupported cases --------------------------------------------------
// The implementation field is named "refusal". It identifies an input outside
// the small finite fragment supported by a sampling method, not a runtime
// failure.

var REFUSE = {
  functions: "the input uses function terms (nested terms as arguments), " +
             "which sampling does not support.",
  builtin: "the input uses arithmetic, equality or another built-in, which " +
           "sampling does not support.",
  // a named priority is ["$", name] in the export: tax(bird) and a bare
  // name look the same there. Clause-activation sampling lets gk handle them
  // in each world; the shared-threshold model compares priorities itself.
  namedpriority: "the input uses named blocker priorities instead of " +
                 "numbers; shared-threshold sampling compares numeric " +
                 "priorities only.",
  noquery: "no query found in the input.",
  multilit: "sampling supports single-literal questions only.",
  toobig: "grounding this input produces over 100000 clauses; sampling is " +
          "limited to small inputs.",
  clausify: "could not obtain clauses from gk (unexpected clausifier output).",
  dbfull: "a sampled world did not fit the solver database in the browser; " +
          "sampling is limited to small inputs.",
  thrOpen: "shared-threshold sampling needs a question without variables.",
  thrDirectional: "shared-threshold sampling supports only directional rules " +
                  "with a single conclusion."
};

var MAX_GROUND = 100000;

function refusal(text) {
  var e = new Error(text);
  e.mcRefusal = text;
  return e;
}

// ---- deterministic random numbers ---------------------------------------
// Port of the seeding in gkmc.Runner.sample: world t is drawn from a
// generator seeded by the string "<seed>:<t>", so the same world can be
// rebuilt later by any worker, in any phase, without shipping it around.
// Python seeds random.Random with that string; JavaScript has no seedable
// generator, so the string is hashed (FNV-1a) into mulberry32. The sampled
// worlds are therefore statistically the same, not bit-identical.

function fnv1a32(s) {
  var h = 0x811c9dc5;
  for (var i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return h >>> 0;
}

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    var t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function rngFor(seed, trial) { return mulberry32(fnv1a32(seed + ":" + trial)); }

// ---- term walking (port of gkmc walk_atom / walk_atom_args / clause_vars /
//      clause_consts / substitute) -----------------------------------------

var OK_DOLLAR = { "$block": 1, "$not": 1, "$ans": 1 };

function stripSign(pred) {
  return (typeof pred === "string" && pred.charAt(0) === "-")
    ? pred.substring(1) : pred;
}

// One argument position: constants and variables through the callbacks,
// nested lists rejected as function terms.
function walkAtomArgs(term, onConst, onVar) {
  if (typeof term === "string") {
    if (term.indexOf("?:") === 0) onVar(term);
    else if (term.charAt(0) !== "$") onConst(term);
    return;
  }
  if (typeof term === "number") { onConst(term); return; }
  if (!Array.isArray(term) || !term.length) return;
  if (term[0] === "$not") {
    for (var i = 1; i < term.length; i++) walkAtom(term[i], onConst, onVar);
    return;
  }
  throw refusal(REFUSE.functions);
}

// One literal: ["pred", arg...], ["$block", strength, atom], or a bare
// propositional string.
function walkAtom(atom, onConst, onVar) {
  if (typeof atom === "string") {
    if (stripSign(atom).charAt(0) === "$") throw refusal(REFUSE.builtin);
    return;
  }
  if (!Array.isArray(atom) || !atom.length) return;
  if (atom[0] === "$block") {
    // the priority (atom[1]) is gk's business: clause-activation sampling hands the
    // blocker back to gk unchanged in every world
    for (var i = 2; i < atom.length; i++) walkAtom(atom[i], onConst, onVar);
    return;
  }
  if (atom[0] === "$not") {
    for (var j = 1; j < atom.length; j++) walkAtom(atom[j], onConst, onVar);
    return;
  }
  var pred = atom[0];
  if (typeof pred === "string") {
    var bare = stripSign(pred);
    if (bare === "=" || bare === "!=") throw refusal(REFUSE.builtin);
    if (bare.charAt(0) === "$" && !OK_DOLLAR[bare]) throw refusal(REFUSE.builtin);
  }
  for (var k = 1; k < atom.length; k++) walkAtomArgs(atom[k], onConst, onVar);
}

// gkmc's walk helpers expect a list of literals; wrap a single-literal fact
// (port of threshold_worlds._as_clause, extended to a bare string literal).
function asClause(logic) {
  if (typeof logic === "string") return [logic];
  if (Array.isArray(logic) && logic.length && typeof logic[0] === "string"
      && logic[0] !== "$block" && logic[0] !== "$not")
    return [logic];
  return logic;
}

function clauseVars(clause) {
  var vs = {};
  var cl = asClause(clause);
  for (var i = 0; i < cl.length; i++)
    walkAtom(cl[i], function () {}, function (v) { vs[v] = 1; });
  return Object.keys(vs).sort();
}

function clauseConsts(clause, acc) {
  var cl = asClause(clause);
  for (var i = 0; i < cl.length; i++)
    walkAtom(cl[i], function (c) { acc[typeof c + ":" + c] = c; },
             function () {});
}

function substitute(term, sub) {
  if (typeof term === "string")
    return Object.prototype.hasOwnProperty.call(sub, term) ? sub[term] : term;
  if (Array.isArray(term)) {
    var out = new Array(term.length);
    for (var i = 0; i < term.length; i++) out[i] = substitute(term[i], sub);
    return out;
  }
  return term;
}

// Constants in gkmc's order: sorted by their string form.
function sortedConsts(acc) {
  var vals = [];
  for (var k in acc) if (Object.prototype.hasOwnProperty.call(acc, k))
    vals.push(acc[k]);
  vals.sort(function (a, b) {
    var sa = String(a), sb = String(b);
    return sa < sb ? -1 : (sa > sb ? 1 : 0);
  });
  return vals;
}

// Every tuple of consts of the given length, calling cb for each; cb may
// return false to stop.
function eachTuple(consts, n, cb) {
  if (n === 0) { cb([]); return; }
  var idx = new Array(n), i;
  for (i = 0; i < n; i++) idx[i] = 0;
  var nc = consts.length;
  if (!nc) return;
  for (;;) {
    var tup = new Array(n);
    for (i = 0; i < n; i++) tup[i] = consts[idx[i]];
    if (cb(tup) === false) return;
    var p = n - 1;
    while (p >= 0) {
      idx[p]++;
      if (idx[p] < nc) break;
      idx[p] = 0; p--;
    }
    if (p < 0) return;
  }
}

// ---- the clause export (port of gkmc.load_clausified) --------------------

// Parse the output of `gk input -defworlds -clausify -outformat json` and
// return its clause items. gk owns the clausifier and the input-weight split;
// this tool only consumes that serialization and fails loudly on drift.
function parseClauseExport(text) {
  var arr;
  try { arr = JSON.parse(text); } catch (e) { throw refusal(REFUSE.clausify); }
  // a syntax error in the text box: say what gk said, with the temporary
  // file name it read from removed
  if (arr && !Array.isArray(arr) && arr.error)
    throw refusal("gk could not read the input: " +
                  String(arr.error).replace(/^input:/, "line "));
  if (!Array.isArray(arr) || !arr.length || !arr[0]
      || arr[0].format !== "gk_clauses_v1")
    throw refusal(REFUSE.clausify);
  var items = [];
  for (var i = 1; i < arr.length; i++) {
    // gk appends the negated question as a separate goal item: not an input
    // statement and not a question of its own.
    if (arr[i]["@name"] === "$auto_negated_question") continue;
    items.push(arr[i]);
  }
  return items;
}

// Consecutive items sharing an @name come from one input statement
// (port of the run grouping in gkmc.ground_pool).
function nameRuns(items) {
  var runs = [];
  for (var i = 0; i < items.length; i++) {
    var name = items[i]["@name"] || "";
    if (runs.length && runs[runs.length - 1].name === name)
      runs[runs.length - 1].items.push(items[i]);
    else runs.push({ name: name, items: [items[i]] });
  }
  return runs;
}

// ---- clause-activation sampling: ground pool (port of gkmc.ground_pool) ---

// Returns {pool, goals, warnings}. pool entries are
// {s: statement index, c: weight, cl: ground clause}: `s` groups the
// ground instances of one input statement, which is what shared draws need.
function groundPool(items) {
  var runs = nameRuns(items);
  var consts = {};
  var i, j;
  for (i = 0; i < items.length; i++) clauseConsts(items[i]["@logic"], consts);
  var cs = sortedConsts(consts);
  if (!cs.length) cs = ["c0"];    // degenerate: fully propositional input

  var pool = [], goals = [], warnings = [];
  var total = 0;
  for (i = 0; i < runs.length; i++) {
    var run = runs[i];
    var isGoal = false;
    for (j = 0; j < run.items.length; j++)
      if (run.items[j]["@role"] === "goal") isGoal = true;
    if (isGoal) {
      for (j = 0; j < run.items.length; j++) goals.push(run.items[j]["@logic"]);
      continue;
    }
    // gk splits a statement's weight over the clauses it produces (the
    // split need not be even), so the drawn values differ from the number in
    // the input; say so when it happens.
    var uncertainSplit = false;
    for (j = 0; j < run.items.length; j++)
      if (numConf(run.items[j]["@confidence"]) < 1.0) uncertainSplit = true;
    if (run.items.length > 1 && uncertainSplit) {
      var parts = [], joint = 1.0;
      for (j = 0; j < run.items.length; j++) {
        var cj = numConf(run.items[j]["@confidence"]);
        parts.push(fmtConf(cj));
        joint *= cj;
      }
      warnings.push("statement " + run.name + " splits into " +
                    run.items.length + " clauses, drawn separately at " +
                    "weights " + parts.join(", ") + "; together they " +
                    "carry the stated " + fmtConf(joint) + ".");
    }
    var seen = {};
    for (j = 0; j < run.items.length; j++) {
      var logic = run.items[j]["@logic"];
      var cconf = numConf(run.items[j]["@confidence"]);
      var vs = clauseVars(logic);
      var stopped = false;
      eachTuple(cs, vs.length, function (tup) {
        var sub = {};
        for (var v = 0; v < vs.length; v++) sub[vs[v]] = tup[v];
        var g = substitute(logic, sub);
        var key = JSON.stringify(g);
        if (seen[key]) return true;
        seen[key] = 1;
        pool.push({ s: i, c: cconf, cl: g });
        total++;
        if (total > MAX_GROUND) { stopped = true; return false; }
        return true;
      });
      if (stopped) throw refusal(REFUSE.toobig);
    }
  }
  if (!goals.length) throw refusal(REFUSE.noquery);
  return { pool: pool, goals: goals, warnings: warnings };
}

function numConf(v) {
  if (v === undefined || v === null) return 1.0;
  var f = parseFloat(v);
  if (isNaN(f)) return 1.0;
  // gk prints float32 values (0.89999997...); round to a sane display and
  // draw value. Confidences above 1 are percentages in the input syntax, but
  // gk has already normalised them by the time they reach the export.
  return Math.round(f * 1e6) / 1e6;
}

function fmtConf(c) {
  var s = c.toFixed(4).replace(/0+$/, "").replace(/\.$/, "");
  return s === "" ? "0" : s;
}

// ---- the question (reconstruction from the exported goal clause) ---------
// gkmc.py writes the original @question item into every world; the clause
// export has only the negated goal clause, so the question is rebuilt from
// it: drop the $ans literal, require a single remaining literal, flip its
// sign. gk accepts the ?:N variables of the export in a JSON question.

function flipSign(lit) {
  if (typeof lit === "string")
    return lit.charAt(0) === "-" ? lit.substring(1) : "-" + lit;
  var out = lit.slice();
  out[0] = (typeof lit[0] === "string" && lit[0].charAt(0) === "-")
    ? lit[0].substring(1) : "-" + lit[0];
  return out;
}

function questionFromGoal(goalClause) {
  var cl = asClause(goalClause);
  var lits = [];
  for (var i = 0; i < cl.length; i++) {
    var lit = cl[i];
    if (Array.isArray(lit) && (lit[0] === "$ans" || lit[0] === "-$ans")) continue;
    lits.push(lit);
  }
  if (lits.length !== 1) throw refusal(REFUSE.multilit);
  return flipSign(lits[0]);
}

// ?:vars of a question literal in first-occurrence order -- the order in
// which gk lists their bindings in the $ans literal
// (port of gkmc.question_var_order).
function questionVarOrder(q) {
  var seen = [];
  (function walk(t) {
    if (typeof t === "string") {
      if (t.indexOf("?:") === 0 && seen.indexOf(t) < 0) seen.push(t);
    } else if (Array.isArray(t)) {
      for (var i = 0; i < t.length; i++) walk(t[i]);
    }
  })(q);
  return seen;
}

// The closed positive and negated instances of the question for one answer
// (port of gkmc.question_instances). Both sides of the pairing are decided
// from closed instances: an open question is unreliable in a contradictory
// world, where the unit carrying the answer can be simplified away before
// the open goal uses it.
function questionInstances(q, values) {
  var vars = questionVarOrder(q);
  if (values.length !== vars.length)
    throw new Error("answer has " + values.length + " bindings but the " +
                    "question has " + vars.length + " variables");
  var sub = {};
  for (var i = 0; i < vars.length; i++) sub[vars[i]] = values[i];
  var inst = substitute(q, sub);
  return { pos: inst, neg: flipSign(inst) };
}

// ---- worlds (port of gkmc.Runner.sample / world_doc / parse_world_answers)

// The world of trial t: every certain clause, plus each uncertain one drawn
// with probability equal to its input weight. Deterministic in (seed, t).
function sampleWorld(pool, seed, trial, draws) {
  var rng = rngFor(seed, trial);
  var active = [], shared = {};
  for (var i = 0; i < pool.length; i++) {
    var e = pool[i];
    if (e.c >= 1.0) { active.push(e.cl); continue; }
    var ok;
    if (draws === "shared") {
      if (!Object.prototype.hasOwnProperty.call(shared, e.s))
        shared[e.s] = rng() < e.c;
      ok = shared[e.s];
    } else {
      ok = rng() < e.c;
    }
    if (ok) active.push(e.cl);
  }
  return active;
}

function worldDoc(active, questions) {
  var doc = [];
  for (var i = 0; i < active.length; i++)
    doc.push({ "@name": "w" + i, "@logic": active[i] });
  for (var j = 0; j < questions.length; j++)
    doc.push({ "@question": questions[j] });
  return JSON.stringify(doc);
}

// World runs decide PURE PROVABILITY (with defaults and blockers): gk's own
// negative-evidence subtraction must not run, or a contradictory world would
// report "evidence below limit" instead of "provable". -plain tells gk the
// world has no input weights.
var WORLD_ARGS = ["input", "-nonegative", "-plain", "-seconds", "2"];

// The answer keys proved in one world, or null when the world could not be
// decided (time limit, error). Port of parse_world_answers + norm_key onto
// the JSON output that JSON input produces. `vals`, when given, collects the
// raw bindings behind each answer key for the later pairing pass.
function parseWorldAnswers(out, vals) {
  var o;
  try { o = JSON.parse(out); } catch (e) { return null; }
  if (!o || typeof o !== "object") return null;
  if (o.error) {
    // a database too small for this world is not a sampling result: stop
    // rather than report the world as a timeout
    if (String(o.error).indexOf("memory") >= 0) throw refusal(REFUSE.dbfull);
    return null;
  }
  var res = o.result || "";
  if (res.indexOf("time limit") >= 0) return null;
  var keys = [];
  var answers = o.answers || [];
  for (var i = 0; i < answers.length; i++) {
    var k = answerKey(answers[i].answer, vals);
    if (k !== null && keys.indexOf(k) < 0) keys.push(k);
  }
  return keys;
}

// "yes" for a proved closed question, the joined $ans bindings for an open
// one, null when the answer does not prove the question.
function answerKey(a, vals) {
  if (a === true) return "yes";
  if (a === false || a === undefined || a === null) return null;
  var args = ansArgs(a);
  if (args === null) return null;
  if (!args.length) return "yes";
  var key = args.map(String).join(",");
  if (vals && !Object.prototype.hasOwnProperty.call(vals, key)) vals[key] = args;
  return key;
}

function ansArgs(a) {
  if (!Array.isArray(a)) return null;
  if (a.length && a[0] === "$ans") return a.slice(1);
  for (var i = 0; i < a.length; i++) {
    var lit = a[i];
    if (Array.isArray(lit) && lit.length && lit[0] === "$ans")
      return lit.slice(1);
  }
  return null;
}

// Decide one world against the given questions.
function decideWorld(pool, seed, trial, draws, questions, vals) {
  var active = sampleWorld(pool, seed, trial, draws);
  var doc = worldDoc(active, questions);
  var out = gkRun([{ name: "input", data: doc }], WORLD_ARGS);
  return parseWorldAnswers(out, vals);
}

// ---- statistics (ports of gkmc.wilson / gkmc.paired_diff_ci) -------------

function wilson(k, n, z) {
  z = z || 1.96;
  if (!n) return [0.0, 0.0];
  var p = k / n;
  var d = 1 + z * z / n;
  var c = (p + z * z / (2 * n)) / d;
  var h = z * Math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d;
  return [Math.max(0.0, c - h), Math.min(1.0, c + h)];
}

// Normal-approximation interval for P(pos)-P(neg) estimated on the SAME
// worlds: the both/neither cells cancel, so the difference is
// (pos_only-neg_only)/n with variance (p1+p2-(p1-p2)^2)/n. Wilson does not
// apply to a difference.
function pairedDiffCi(posOnly, negOnly, n, z) {
  z = z || 1.96;
  if (!n) return { diff: 0.0, lo: 0.0, hi: 0.0 };
  var p1 = posOnly / n, p2 = negOnly / n;
  var diff = p1 - p2;
  var se = Math.sqrt(Math.max(0.0, p1 + p2 - diff * diff) / n);
  return { diff: diff, lo: diff - z * se, hi: diff + z * se };
}

// ==========================================================================
// shared-threshold sampling -- port of montecarlo/threshold_worlds.py
// ==========================================================================
//
// Each ground atom with evidence draws one acceptance threshold U in [0,1].
// Positive evidence for the atom is pooled (noisy-or) into strength a,
// negative evidence into b, and the SAME U decides both polarities:
//
//   supported for      iff  b < U <= a
//   supported against  iff  a < U <= b
//   conflict           iff  U <= min(a, b)
//   ignorance          iff  U >  max(a, b)
//
// A shared atom has one threshold, so evidence passing through the same atom
// stays correlated. Cases the model does not settle are reported as not
// scored instead of guessed.

// An atom is {p: predicate, a: [args], k: key}; k identifies it in maps and
// sorts, taking the place of Python's tuple keys.
function mkAtom(pred, args) {
  return { p: pred, a: args, k: pred + " " + JSON.stringify(args) };
}

function atomText(atom) {
  return atom.a.length ? atom.p + "(" + atom.a.map(String).join(",") + ")"
                       : atom.p;
}

function splitSign(pred) {
  if (typeof pred === "string" && pred.charAt(0) === "-")
    return { pred: pred.substring(1), sign: "-" };
  return { pred: pred, sign: "+" };
}

function complement(sign) { return sign === "+" ? "-" : "+"; }

// Port of threshold_worlds._priority: taxonomy strengths are not modelled.
function priorityOf(strength) {
  return (typeof strength === "number" && strength === Math.floor(strength))
    ? strength : 0;
}

function atomOf(lit) {
  if (typeof lit === "string") return mkAtom(splitSign(lit).pred, []);
  return mkAtom(splitSign(lit[0]).pred, lit.slice(1));
}

// Port of threshold_worlds.parse_literal. Returns
//   {kind:"block", prio, batom, bsign} or {kind:"lit", sign, atom}.
function parseLiteral(lit) {
  if (typeof lit === "string") {
    if (stripSign(lit).charAt(0) === "$") throw refusal(REFUSE.builtin);
    var ss = splitSign(lit);
    return { kind: "lit", sign: ss.sign, atom: mkAtom(ss.pred, []) };
  }
  if (Array.isArray(lit) && lit.length && lit[0] === "$block") {
    // port of threshold_worlds._validate_clause: a named priority cannot be
    // ordered against the numeric ones this model compares
    if (Array.isArray(lit[1])) throw refusal(REFUSE.namedpriority);
    var target = lit[2];
    if (Array.isArray(target) && target.length && target[0] === "$not")
      return { kind: "block", prio: priorityOf(lit[1]),
               batom: atomOf(target[1]), bsign: "-" };
    return { kind: "block", prio: priorityOf(lit[1]),
             batom: atomOf(target), bsign: "+" };
  }
  if (!(Array.isArray(lit) && lit.length && typeof lit[0] === "string"))
    throw refusal(REFUSE.thrDirectional);
  var bare = stripSign(lit[0]);
  if (bare === "=" || bare === "!=") throw refusal(REFUSE.builtin);
  if (bare.charAt(0) === "$" && !OK_DOLLAR[bare]) throw refusal(REFUSE.builtin);
  for (var i = 1; i < lit.length; i++)
    if (Array.isArray(lit[i])) throw refusal(REFUSE.functions);
  var s = splitSign(lit[0]);
  return { kind: "lit", sign: s.sign, atom: mkAtom(s.pred, lit.slice(1)) };
}

// Port of threshold_worlds._implied_positions: which ordinary-literal
// positions are the implied (head) literals of a clause, mirroring gk's
// dw_build_index stack.
//   case 2 -- a $block whose content atom's COMPLEMENT (same functor,
//             opposite sign) is an ordinary literal marks THAT literal as the
//             single head;
//   case 1 -- otherwise every POSITIVE ordinary literal is a head (a
//             non-Horn disjunction delivers either);
//   residual -- an all-negative clause takes the @head marker; -1 there is
//             the marker-less tripwire, which is declined rather than guessed.
function impliedPositions(ordLits, blocks, headIdx) {
  var pos, b;
  for (b = 0; b < blocks.length; b++) {
    for (pos = 0; pos < ordLits.length; pos++) {
      // gk compares FUNCTOR, not arguments
      if (ordLits[pos].atom.p === blocks[b].batom.p
          && ordLits[pos].sign !== blocks[b].bsign)
        return [pos];
    }
  }
  var posIdx = [];
  for (pos = 0; pos < ordLits.length; pos++)
    if (ordLits[pos].sign === "+") posIdx.push(pos);
  if (posIdx.length) return posIdx;
  if (headIdx !== undefined && headIdx !== null && headIdx >= 0) {
    for (pos = 0; pos < ordLits.length; pos++)
      if (ordLits[pos].i === headIdx) return [pos];
  }
  return null;       // marker-less: the caller declines to score
}

// Port of threshold_worlds._orient_head_last: one template per implied
// literal, with the chosen head moved LAST among the ordinary literals, so
// the last-literal convention of clauseLiterals picks the head gk picks.
function orientHeadLast(logic, headIdx) {
  if (typeof logic === "string") return [logic];
  if (Array.isArray(logic) && logic.length && typeof logic[0] === "string"
      && logic[0] !== "$block" && logic[0] !== "$not")
    return [logic];                       // fact: single positive unit
  var ordLits = [], blocks = [], markers = [], i;
  for (i = 0; i < logic.length; i++) {
    var item = logic[i];
    var kind = parseLiteral(item);
    if (kind.kind === "block") {
      blocks.push({ i: i, batom: kind.batom, bsign: kind.bsign });
      markers.push(item);
    } else if (Array.isArray(item) && item.length && item[0] === "$ans") {
      markers.push(item);                 // answer literal: not a head
    } else {
      ordLits.push({ i: i, sign: kind.sign, atom: kind.atom });
    }
  }
  if (!ordLits.length) return [logic];
  var ordItems = ordLits.map(function (o) { return logic[o.i]; });
  var heads = impliedPositions(ordLits, blocks, headIdx);
  if (heads === null) return null;        // marker-less tripwire
  var templates = [];
  for (var h = 0; h < heads.length; h++) {
    var hpos = heads[h];
    var rest = [];
    for (i = 0; i < ordItems.length; i++) if (i !== hpos) rest.push(ordItems[i]);
    templates.push(rest.concat(markers, [ordItems[hpos]]));
  }
  return templates;
}

// Port of threshold_worlds.ground_clausified: ground the export over the
// Herbrand constants of the NON-goal clauses (parity with gk's
// dw_collect_constpool: a constant appearing only in the query is not a
// witness). Strengths come straight from @confidence.
function groundClausified(items) {
  var consts = {}, axioms = [], i;
  for (i = 0; i < items.length; i++) {
    if (items[i]["@role"] === "goal") continue;
    clauseConsts(items[i]["@logic"], consts);
    axioms.push(items[i]);
  }
  var cs = sortedConsts(consts);
  if (!cs.length) cs = ["c0"];
  var pool = [], total = 0;
  for (i = 0; i < axioms.length; i++) {
    var logic = axioms[i]["@logic"];
    var conf = numConf(axioms[i]["@confidence"]);
    var templates = orientHeadLast(logic, axioms[i]["@head"]);
    if (templates === null) throw refusal(REFUSE.thrDirectional);
    for (var t = 0; t < templates.length; t++) {
      var tmpl = templates[t];
      var vs = clauseVars(tmpl);
      var seen = {}, stopped = false;
      eachTuple(cs, vs.length, function (tup) {
        var sub = {};
        for (var v = 0; v < vs.length; v++) sub[vs[v]] = tup[v];
        var g = substitute(tmpl, sub);
        var key = JSON.stringify(g);
        if (seen[key]) return true;
        seen[key] = 1;
        pool.push({ c: conf, cl: g });
        total++;
        if (total > MAX_GROUND) { stopped = true; return false; }
        return true;
      });
      if (stopped) throw refusal(REFUSE.toobig);
    }
  }
  return pool;
}

// Port of threshold_worlds.clause_literals: split a ground clause into
// ordinary literals and block markers. The HEAD is the last ordinary literal
// (the convention orientHeadLast has just established).
function clauseLiterals(raw) {
  if (typeof raw === "string" ||
      (Array.isArray(raw) && raw.length && typeof raw[0] === "string"
       && raw[0] !== "$block" && raw[0] !== "$not")) {
    var k = parseLiteral(raw);
    return { lits: [k], blocks: [] };
  }
  var lits = [], blocks = [];
  for (var i = 0; i < raw.length; i++) {
    var kind = parseLiteral(raw[i]);
    if (kind.kind === "block")
      blocks.push({ prio: kind.prio, batom: kind.batom, bsign: kind.bsign });
    else lits.push(kind);
  }
  return { lits: lits, blocks: blocks };
}

// Port of threshold_worlds.build_testimonies: the directional testimonies
// reachable from the query by backward chaining. Indexing by head ATOM
// collects both polarities of a contested atom without generating spurious
// reverse rules.
function buildTestimonies(pool, queryAtom) {
  var byHeadAtom = {}, i, j;
  for (i = 0; i < pool.length; i++) {
    var split = clauseLiterals(pool[i].cl);
    if (!split.lits.length) continue;
    var head = split.lits[split.lits.length - 1];
    var body = [];
    for (j = 0; j < split.lits.length - 1; j++)
      body.push({ atom: split.lits[j].atom,
                  sign: complement(split.lits[j].sign) });
    var distBlk = [], mutual = [];
    for (j = 0; j < split.blocks.length; j++) {
      var b = split.blocks[j];
      if (b.batom.k === head.atom.k) mutual.push({ prio: b.prio, sign: b.bsign });
      else distBlk.push({ atom: b.batom, sign: b.bsign, prio: b.prio });
    }
    if (!byHeadAtom[head.atom.k]) byHeadAtom[head.atom.k] = [];
    byHeadAtom[head.atom.k].push({
      headAtom: head.atom, headSign: head.sign, strength: pool[i].c,
      body: body, blockers: distBlk, mutual: mutual, pairedMain: false
    });
  }
  var testimonies = [], atoms = {}, frontier = [queryAtom];
  while (frontier.length) {
    var atom = frontier.pop();
    if (atoms[atom.k]) continue;
    atoms[atom.k] = atom;
    var ts = byHeadAtom[atom.k] || [];
    for (i = 0; i < ts.length; i++) {
      testimonies.push(ts[i]);
      for (j = 0; j < ts[i].body.length; j++) frontier.push(ts[i].body[j].atom);
      for (j = 0; j < ts[i].blockers.length; j++)
        frontier.push(ts[i].blockers[j].atom);
    }
  }
  markPairs(testimonies);
  return { testimonies: testimonies, atoms: atoms };
}

// Port of threshold_worlds._mark_pairs: a rule-instance contribution (stored
// in `testimonies`) is paired with a main rule when they have opposite heads
// for one atom and the main rule's exception condition occurs in its body.
function markPairs(testimonies) {
  var byAtom = {}, i;
  for (i = 0; i < testimonies.length; i++) {
    var t = testimonies[i];
    if (!byAtom[t.headAtom.k]) byAtom[t.headAtom.k] = [];
    byAtom[t.headAtom.k].push(t);
  }
  for (var k in byAtom) if (Object.prototype.hasOwnProperty.call(byAtom, k)) {
    var ts = byAtom[k];
    for (i = 0; i < ts.length; i++) {
      var main = ts[i];
      if (!main.blockers.length) continue;
      var blkAtoms = {};
      for (var b = 0; b < main.blockers.length; b++)
        blkAtoms[main.blockers[b].atom.k] = 1;
      for (var j = 0; j < ts.length; j++) {
        var exc = ts[j];
        if (exc.headSign === main.headSign) continue;
        for (var y = 0; y < exc.body.length; y++)
          if (blkAtoms[exc.body[y].atom.k]) { exc.pairedMain = true; break; }
      }
    }
  }
}

// Port of threshold_worlds._present.
function present(t, state) {
  var i, st;
  for (i = 0; i < t.body.length; i++) {
    st = state[t.body[i].atom.k] || [false, false];
    if (!(t.body[i].sign === "+" ? st[0] : st[1])) return false;
  }
  for (i = 0; i < t.blockers.length; i++) {
    st = state[t.blockers[i].atom.k] || [false, false];
    if (t.blockers[i].sign === "+" ? st[0] : st[1]) return false;
  }
  return true;
}

// Port of threshold_worlds._pools: pooled positive/negative strengths of the
// PRESENT rule-instance contributions, the paired-exception residual fill,
// and each polarity's mutual-block rank. A polarity's rank is the maximum
// mutual-block rank of its present contributions when every contribution in
// that polarity comes from a ranked default. It is 0 when any present
// contribution is unranked, and -1 when there is no present contribution.
function poolsOf(ts, state) {
  var pro = [], con = [], filled = false, rankPro = -1, rankCon = -1, i, j;
  var mainProBlocked = false;
  for (i = 0; i < ts.length; i++)
    if (ts[i].headSign === "+" && ts[i].blockers.length && !present(ts[i], state))
      mainProBlocked = true;
  for (i = 0; i < ts.length; i++) {
    var t = ts[i];
    if (!present(t, state)) continue;
    var trank = 0;
    for (j = 0; j < t.mutual.length; j++)
      trank = Math.max(trank, t.mutual[j].prio);
    if (t.headSign === "+") {
      pro.push(t.strength);
      rankPro = (trank < 1 || rankPro === 0) ? 0 : Math.max(rankPro, trank);
    } else {
      con.push(t.strength);
      rankCon = (trank < 1 || rankCon === 0) ? 0 : Math.max(rankCon, trank);
      if (t.pairedMain && mainProBlocked) filled = true;
    }
  }
  var a = 1.0, b = 1.0;
  for (i = 0; i < pro.length; i++) a *= (1 - pro[i]);
  a = 1 - a;
  for (i = 0; i < con.length; i++) b *= (1 - con[i]);
  b = 1 - b;
  return { a: a, b: b, filled: filled, rankPro: rankPro, rankCon: rankCon };
}

// Port of threshold_worlds._net: (pro_usable, con_usable, conflict) for one
// atom in one world. u2 = [uPro, uCon]: two independent uniforms per atom.
// Ordinary opposition uses the SHARED threshold uPro for both polarities;
// default interactions use both thresholds:
//
//   opposed defaults, unequal ranks -> strict-priority override (the
//     higher-ranked polarity takes the overlap, the lower keeps its excess);
//   opposed defaults, equal ranks   -> mutual blocking: each polarity fires
//     on its own threshold and survives only if the other missed;
//   default opposed by ordinary evidence -> exclusive outcome regions: the
//     ordinary polarity fires on its threshold, and the default survives only
//     where the ordinary evidence misses; no conflict component.
//
// The independent second threshold is what makes for = a(1-b) a product; a
// single shared threshold cannot express it.
function netOf(p, u2) {
  var ul = u2[0], ur = u2[1];
  var lo = Math.min(p.a, p.b);
  var gatedPro = (p.rankPro >= 1), gatedCon = (p.rankCon >= 1);
  if (p.a > 0 && p.b > 0 && gatedPro && gatedCon && p.rankPro !== p.rankCon) {
    if (p.rankPro > p.rankCon)
      return { pro: ul <= p.a, con: p.a < ul && ul <= p.b, conflict: false };
    return { pro: p.b < ul && ul <= p.a, con: ul <= p.b, conflict: false };
  }
  if (p.a > 0 && p.b > 0 && gatedPro && gatedCon) {
    // equal ranks: both-fire and neither-fire are ignorance (the certain
    // limit is full ignorance from equal-priority mutual blocking)
    var fp = ul <= p.a, fc = ur <= p.b;
    return { pro: fp && !fc, con: fc && !fp, conflict: false };
  }
  if (p.a > 0 && p.b > 0 && gatedPro) {
    var fc1 = ur <= p.b;
    return { pro: (ul <= p.a) && !fc1, con: fc1, conflict: false };
  }
  if (p.a > 0 && p.b > 0 && gatedCon) {
    // mirror: the refuting side is the gated one
    var fp1 = ul <= p.a;
    return { pro: fp1, con: (ur <= p.b) && !fp1, conflict: false };
  }
  var pro = (p.b < ul && ul <= p.a);
  var con = (p.a < ul && ul <= p.b);
  var conflict = (ul <= lo);
  if (p.filled && ul > p.b && !pro) pro = true;   // residual fill
  return { pro: pro, con: con, conflict: conflict && !pro && !con };
}

function evalAtom(ts, state, u, atomKey) {
  var r = netOf(poolsOf(ts, state), u[atomKey]);
  return [r.pro, r.con];
}

// Port of threshold_worlds._atom_deps: head atom -> body and distinct-atom
// blocker atoms. Mutual (same-atom) blocks are self-loops and ignored.
function atomDeps(testimonies, atoms) {
  var deps = {}, k;
  for (k in atoms) if (Object.prototype.hasOwnProperty.call(atoms, k))
    deps[k] = {};
  for (var i = 0; i < testimonies.length; i++) {
    var t = testimonies[i], j;
    for (j = 0; j < t.body.length; j++)
      if (t.body[j].atom.k !== t.headAtom.k)
        deps[t.headAtom.k][t.body[j].atom.k] = 1;
    for (j = 0; j < t.blockers.length; j++)
      if (t.blockers[j].atom.k !== t.headAtom.k)
        deps[t.headAtom.k][t.blockers[j].atom.k] = 1;
  }
  return deps;
}

// Port of threshold_worlds._topo_order: Kahn sort, null on a genuine cycle.
function topoOrder(deps, atomKeys) {
  var indeg = {}, rdeps = {}, k, d;
  for (var i = 0; i < atomKeys.length; i++) {
    k = atomKeys[i];
    indeg[k] = Object.keys(deps[k] || {}).length;
    rdeps[k] = rdeps[k] || [];
  }
  for (i = 0; i < atomKeys.length; i++) {
    k = atomKeys[i];
    for (d in deps[k]) if (Object.prototype.hasOwnProperty.call(deps[k], d)) {
      rdeps[d] = rdeps[d] || [];
      rdeps[d].push(k);
    }
  }
  var order = [], ready = [];
  for (i = 0; i < atomKeys.length; i++)
    if (!indeg[atomKeys[i]]) ready.push(atomKeys[i]);
  while (ready.length) {
    k = ready.pop();
    order.push(k);
    var rs = rdeps[k] || [];
    for (i = 0; i < rs.length; i++) {
      indeg[rs[i]]--;
      if (!indeg[rs[i]]) ready.push(rs[i]);
    }
  }
  return order.length === atomKeys.length ? order : null;
}

// Port of threshold_worlds._sccs: iterative Tarjan, dependency-first.
function sccs(deps, atomKeys) {
  var index = {}, low = {}, onstack = {}, stack = [], out = [], counter = 0;
  for (var r = 0; r < atomKeys.length; r++) {
    var root = atomKeys[r];
    if (Object.prototype.hasOwnProperty.call(index, root)) continue;
    index[root] = low[root] = counter++;
    stack.push(root); onstack[root] = 1;
    var work = [{ v: root, it: Object.keys(deps[root] || {}), pos: 0 }];
    while (work.length) {
      var fr = work[work.length - 1];
      var pushed = false;
      while (fr.pos < fr.it.length) {
        var w = fr.it[fr.pos++];
        if (!Object.prototype.hasOwnProperty.call(index, w)) {
          index[w] = low[w] = counter++;
          stack.push(w); onstack[w] = 1;
          work.push({ v: w, it: Object.keys(deps[w] || {}), pos: 0 });
          pushed = true;
          break;
        }
        if (onstack[w]) low[fr.v] = Math.min(low[fr.v], index[w]);
      }
      if (pushed) continue;
      work.pop();
      if (work.length) {
        var pv = work[work.length - 1].v;
        low[pv] = Math.min(low[pv], low[fr.v]);
      }
      if (low[fr.v] === index[fr.v]) {
        var comp = [];
        for (;;) {
          var x = stack.pop();
          delete onstack[x];
          comp.push(x);
          if (x === fr.v) break;
        }
        out.push(comp);
      }
    }
  }
  return out;
}

// Port of threshold_worlds._scc_plan: the SCC condensation in
// dependency-first order. The per-world fixpoint is monotone -- hence unique
// and equal to the derivability reading -- ONLY when the cycle contains no
// blocker and no contested atom, so any other cyclic group is not scored.
function sccPlan(testimonies, atoms, byHead, queryAtom) {
  var atomKeys = Object.keys(atoms).sort();
  var deps = atomDeps(testimonies, atoms);
  var plan = [];
  var comps = sccs(deps, atomKeys);
  for (var c = 0; c < comps.length; c++) {
    var comp = comps[c];
    if (comp.length === 1) { plan.push(comp); continue; }
    var cset = {}, i;
    for (i = 0; i < comp.length; i++) cset[comp[i]] = 1;
    for (i = 0; i < comp.length; i++) {
      var ts = byHead[comp[i]] || [], signs = {};
      for (var j = 0; j < ts.length; j++) signs[ts[j].headSign] = 1;
      if (Object.keys(signs).length > 1)
        return { plan: null, why: "contested atom " + atomText(atoms[comp[i]]) +
                                  " inside a dependency cycle" };
    }
    var hasBlocker = false;
    for (i = 0; i < testimonies.length; i++) {
      var t = testimonies[i];
      if (!cset[t.headAtom.k]) continue;
      for (var b = 0; b < t.blockers.length; b++)
        if (cset[t.blockers[b].atom.k]) hasBlocker = true;
    }
    if (hasBlocker) {
      // a blocker cycle that runs through the QUERY atom resolves credulously
      // for the query: gk's blocker check voids an exception argument whose
      // own validity depends on defeating the queried candidate. Away from
      // the query there is no such reference point, so it stays unscored.
      if (queryAtom && cset[queryAtom.k]) {
        plan.push(["credulous"].concat(comp.slice().sort()));
        continue;
      }
      return { plan: null, why: "blocker cycle away from the query atom; the " +
               "credulous resolution is defined relative to the query only" };
    }
    plan.push(comp.slice().sort());
  }
  return { plan: plan, why: null };
}

// Port of threshold_worlds._eval_scc_credulous: the query atom first with
// every in-group blocker voided, then the remaining atoms by fixpoint given
// that committed state, so the defeated side of the loop comes out blocked.
function evalSccCredulous(comp, queryAtom, byHead, state, u) {
  var cset = {}, i, j;
  for (i = 0; i < comp.length; i++) { cset[comp[i]] = 1; state[comp[i]] = [false, false]; }
  var ts = byHead[queryAtom.k] || [], stripped = [];
  for (i = 0; i < ts.length; i++) {
    var t = ts[i], blk = [];
    for (j = 0; j < t.blockers.length; j++)
      if (!cset[t.blockers[j].atom.k]) blk.push(t.blockers[j]);
    if (blk.length === t.blockers.length) stripped.push(t);
    else stripped.push({ headAtom: t.headAtom, headSign: t.headSign,
                         strength: t.strength, body: t.body, blockers: blk,
                         mutual: t.mutual, pairedMain: t.pairedMain });
  }
  state[queryAtom.k] = evalAtom(stripped, state, u, queryAtom.k);
  var rest = [];
  for (i = 0; i < comp.length; i++)
    if (comp[i] !== queryAtom.k) rest.push(comp[i]);
  for (var pass = 0; pass < 2 * comp.length + 2; pass++) {
    var changed = false;
    for (i = 0; i < rest.length; i++) {
      var nw = evalAtom(byHead[rest[i]] || [], state, u, rest[i]);
      var old = state[rest[i]];
      if (nw[0] !== old[0] || nw[1] !== old[1]) { state[rest[i]] = nw; changed = true; }
    }
    if (!changed) return;
  }
  throw new Error("credulous fixpoint failed to converge");
}

// Port of threshold_worlds._eval_scc_fixpoint: least fixpoint of one
// monotone cyclic component in one world. Atoms whose support needs
// bootstrapping through the cycle stay non-usable: the well-founded reading.
function evalSccFixpoint(comp, byHead, state, u) {
  var i;
  for (i = 0; i < comp.length; i++) state[comp[i]] = [false, false];
  for (var pass = 0; pass < 2 * comp.length + 2; pass++) {
    var changed = false;
    for (i = 0; i < comp.length; i++) {
      var nw = evalAtom(byHead[comp[i]] || [], state, u, comp[i]);
      var old = state[comp[i]];
      if (nw[0] !== old[0] || nw[1] !== old[1]) {
        state[comp[i]] = nw;
        changed = true;
      }
    }
    if (!changed) return;
  }
  throw new Error("fixpoint failed to converge on a monotone component");
}

// Port of threshold_worlds._has_rank_restricted_blocker: a blocker check at
// rank r whose content atom's support flows through a rule self-protected
// strictly below r. gk's search side refuses that support inside the check;
// this model has no rank classes on checks, so the case is flagged.
function hasRankRestrictedBlocker(testimonies, byHead) {
  for (var i = 0; i < testimonies.length; i++) {
    var t = testimonies[i];
    for (var b = 0; b < t.blockers.length; b++) {
      var blk = t.blockers[b];
      var sup = byHead[blk.atom.k] || [];
      for (var s = 0; s < sup.length; s++) {
        if (sup[s].headSign !== blk.sign || !sup[s].mutual.length) continue;
        for (var m = 0; m < sup[s].mutual.length; m++) {
          var mp = sup[s].mutual[m].prio;
          if (mp > 0 && mp < blk.prio)
            return { atom: blk.atom, check: blk.prio, protect: mp };
        }
      }
    }
  }
  return null;
}

// Port of threshold_worlds.evaluate.
function thresholdEvaluate(pool, queryAtom, querySign, trials, seed) {
  var bt = buildTestimonies(pool, queryAtom);
  var testimonies = bt.testimonies, atoms = bt.atoms;
  var byHead = {}, i;
  for (i = 0; i < testimonies.length; i++) {
    var t = testimonies[i];
    if (!byHead[t.headAtom.k]) byHead[t.headAtom.k] = [];
    byHead[t.headAtom.k].push(t);
  }
  var atomKeys = Object.keys(atoms).sort();   // canonical draw order: the seed
  // must fully determine each atom's threshold regardless of map order
  var deps = atomDeps(testimonies, atoms);
  var order = topoOrder(deps, atomKeys);
  var plan = null;
  if (order === null) {
    var sp = sccPlan(testimonies, atoms, byHead, queryAtom);
    // a cycle through a contested atom, or through a blocker away from the
    // query, has no unique fixpoint, so the model reports the case as
    // unsupported (the page prints the reason)
    if (sp.plan === null) return { notScored: sp.why };
    plan = sp.plan;
  }

  // Unequal mutual ranks use the defined strict-priority override and need no
  // annotation. The rank-restricted DISTINCT-atom check remains annotated:
  // this model carries a rule-instance contribution's own mutual rank, not a
  // derivation-deep guard.
  var rankNote = hasRankRestrictedBlocker(testimonies, byHead);
  var tally = { forr: 0, against: 0, conflict: 0, ignorance: 0 };
  var rng = mulberry32(fnv1a32(String(seed)));
  for (var trial = 0; trial < trials; trial++) {
    var u = {};
    // two independent bars per atom, in a canonical order so that the seed
    // fully determines them
    for (i = 0; i < atomKeys.length; i++) u[atomKeys[i]] = [rng(), rng()];
    var state = {};
    if (order !== null) {
      for (i = 0; i < order.length; i++)
        state[order[i]] = evalAtom(byHead[order[i]] || [], state, u, order[i]);
    } else {
      for (i = 0; i < plan.length; i++) {
        if (plan[i].length === 1)
          state[plan[i][0]] = evalAtom(byHead[plan[i][0]] || [], state, u,
                                       plan[i][0]);
        else if (plan[i][0] === "credulous")
          evalSccCredulous(plan[i].slice(1), queryAtom, byHead, state, u);
        else evalSccFixpoint(plan[i], byHead, state, u);
      }
    }
    var r = netOf(poolsOf(byHead[queryAtom.k] || [], state), u[queryAtom.k]);
    var pro = r.pro, con = r.con;
    if (querySign === "-") { var tmp = pro; pro = con; con = tmp; }
    if (pro) tally.forr++;
    else if (con) tally.against++;
    else if (r.conflict) tally.conflict++;
    else tally.ignorance++;
  }
  var out = {
    support_for: tally.forr / trials,
    support_against: tally.against / trials,
    conflict: tally.conflict / trials,
    ignorance: tally.ignorance / trials
  };
  if (rankNote)
    out.priorityNote = "the blocker check at priority " + rankNote.check +
      " targets " + atomText(rankNote.atom) + ", whose support is protected " +
      "at the lower priority " + rankNote.protect + ": gk restricts that " +
      "support, this model does not, so the estimate is made without the " +
      "restriction";
  return out;
}

// The query atom and sign for threshold sampling
// (port of gkmc._query_atom_sign).
function queryAtomSign(q) {
  if (typeof q === "string") {
    if (q.indexOf("?:") === 0) throw refusal(REFUSE.thrOpen);
    var ss = splitSign(q);
    if (ss.pred.charAt(0) === "$") throw refusal(REFUSE.builtin);
    return { atom: mkAtom(ss.pred, []), sign: ss.sign };
  }
  if (!(Array.isArray(q) && q.length && typeof q[0] === "string"))
    throw refusal(REFUSE.multilit);
  var bare = stripSign(q[0]);
  if (bare.charAt(0) === "$" && !OK_DOLLAR[bare]) throw refusal(REFUSE.builtin);
  if (questionVarOrder(q).length) throw refusal(REFUSE.thrOpen);
  for (var i = 1; i < q.length; i++)
    if (Array.isArray(q[i])) throw refusal(REFUSE.functions);
  var s = splitSign(q[0]);
  return { atom: mkAtom(s.pred, q.slice(1)), sign: s.sign };
}

// ==========================================================================
// gk's own numbers (the reference run) and the message handlers
// ==========================================================================

// Parse `gk input -detail -outformat json`: the confidence and the four
// masses per answer, keyed the same way the sampled answers are.
function parseReference(out) {
  var o;
  try { o = JSON.parse(out); } catch (e) { return { result: "", answers: {} }; }
  if (!o || typeof o !== "object") return { result: "", answers: {} };
  var res = { result: o.result || "", answers: {}, order: [] };
  if (o.error) { res.error = o.error; return res; }
  // Answers defeated by exceptions are reported separately by gk; sampling
  // can still prove them in some worlds, so they are kept and marked rather
  // than left out of the comparison.
  var groups = [{ list: o.answers || [], rejected: false },
                { list: o.rejected_answers || [], rejected: true }];
  for (var g = 0; g < groups.length; g++) {
    var answers = groups[g].list;
    for (var i = 0; i < answers.length; i++) {
      var a = answers[i];
      // for a world run a false answer proves nothing, but here it is gk's
      // report that the NEGATION holds: keep it under the question's own key
      // and mark it, so the comparison column is not left empty
      var negated = (a.answer === false);
      var k = negated ? "yes" : answerKey(a.answer, null);
      if (k === null) continue;
      if (!Object.prototype.hasOwnProperty.call(res.answers, k)) {
        res.answers[k] = {
          confidence: (typeof a.confidence === "number") ? a.confidence : null,
          detail: a.detail || null,
          rejected: groups[g].rejected,
          negated: negated
        };
        res.order.push(k);
      }
    }
  }
  return res;
}

// cmd "setup": the reference run, the clause export, the ground pool and the
// eligibility verdict. The order of the two gk calls is fixed (see the file
// header): a plain run first, the clausifier second, world runs only after.
function doSetup(job) {
  var input = job.input;
  var secs = job.seconds ? String(job.seconds) : "5";
  // the reference run is an ordinary solve, exactly as the Solve button runs
  // it, so its numbers are the ones the page shows elsewhere
  var refArgs = ["input", "-detail", "-outformat", "json", "-seconds", secs];
  var refOut = gkRun([{ name: "input", data: input }], refArgs);
  var reference = parseReference(refOut);
  var expOut = gkRun([{ name: "input", data: input }],
                     ["input", "-defworlds", "-clausify", "-outformat", "json"]);
  var items = parseClauseExport(expOut);

  var ground = groundPool(items);
  var questions = [], goalq = [];
  for (var i = 0; i < ground.goals.length; i++)
    goalq.push(questionFromGoal(ground.goals[i]));
  // separate goal statements are separate questions; duplicates (gk's own
  // goal split) collapse
  var seenq = {};
  for (i = 0; i < goalq.length; i++) {
    var key = JSON.stringify(goalq[i]);
    if (seenq[key]) continue;
    seenq[key] = 1;
    questions.push(goalq[i]);
  }

  var reply = {
    ok: true, cmd: "setup",
    reference: reference,
    pool: ground.pool,
    questions: questions,
    warnings: ground.warnings
  };
  if (job.method === "threshold") {
    // the threshold model reads the clauses with its own head orientation
    var qs = queryAtomSign(questions[0]);
    reply.thresholdPool = groundClausified(items);
    reply.queryAtom = qs.atom;
    reply.querySign = qs.sign;
  }
  return reply;
}

// cmd "trials": decide worlds from..to-1 against the question(s). `keys[i]`
// is the list of answer keys proved in world from+i, or null when that world
// could not be decided. `values` maps each key seen to its raw $ans bindings,
// which the pairing pass substitutes back into the question.
function doTrials(job) {
  var keys = [], values = {}, invalid = 0, done = 0, t;
  for (t = job.from; t < job.to; t++) {
    if (retiring()) break;
    var k = decideWorld(job.pool, job.seed, t, job.draws, job.questions, values);
    if (k === null) invalid++;
    keys.push(k);
    done++;
    if (done % 25 === 0)
      post({ cmd: "trials", progress: true, done: done,
             from: job.from, to: job.to });
  }
  return { ok: true, cmd: "trials", from: job.from, to: t, until: job.to,
           keys: keys, values: values, invalid: invalid,
           retire: (t < job.to) };
}

// The solver instance has died (Module.onAbort), so the rest of the range
// needs a fresh worker. This is a safety backstop: one healthy instance
// decides thousands of worlds. The retire protocol ensures that an abort
// degrades to slower sampling instead of a dead run.
function retiring() { return moduleDead; }

// cmd "pair": the per-answer pairing pass. The same worlds are re-generated
// from (seed, trial) and decided against the answer's CLOSED positive and
// negated instances -- gk's own per-answer negative check. Closed instances
// are used on both sides because an open question is unreliable in a
// contradictory world; when the question is already closed, the phase-1
// verdict (posKnown) stands in for the positive run.
function doPair(job) {
  var inst;
  try { inst = questionInstances(job.question, job.values || []); }
  catch (e) {
    return { ok: true, cmd: "pair", answer: job.answer, cells: null, n: 0,
             warning: "answer '" + job.answer + "': " + e.message +
                      "; provability only" };
  }
  var closed = questionVarOrder(job.question).length === 0;
  var cells = { pos_only: 0, neg_only: 0, both: 0, neither: 0 }, n = 0;
  var done = 0, i;
  for (i = 0; i < job.trials.length; i++) {
    if (retiring()) break;
    var t = job.trials[i];
    var p;
    if (closed) {
      p = !!job.posKnown[i];
    } else {
      var kp = decideWorld(job.pool, job.seed, t, job.draws, [inst.pos], null);
      if (kp === null) { done++; continue; }
      p = kp.length > 0;
    }
    var kn = decideWorld(job.pool, job.seed, t, job.draws, [inst.neg], null);
    if (kn === null) { done++; continue; }
    var ng = kn.length > 0;
    cells[p && ng ? "both" : p ? "pos_only" : ng ? "neg_only" : "neither"]++;
    n++;
    done++;
    if (done % 25 === 0)
      post({ cmd: "pair", progress: true, done: done,
             total: job.trials.length, answer: job.answer });
  }
  return { ok: true, cmd: "pair", answer: job.answer, cells: cells, n: n,
           consumed: i, retire: (i < job.trials.length) };
}

// cmd "threshold": the four-component shared-threshold report; no proof search.
function doThreshold(job) {
  var res = thresholdEvaluate(job.pool, job.queryAtom, job.querySign,
                              job.trials, job.seed);
  res.ok = true;
  res.cmd = "threshold";
  res.trials = job.trials;
  return res;
}

function handle(job) {
  var needsGk = (job.cmd === "setup" || job.cmd === "trials"
                 || job.cmd === "pair");
  var run = function () {
    var reply;
    try {
      if (job.cmd === "setup") reply = doSetup(job);
      else if (job.cmd === "trials") reply = doTrials(job);
      else if (job.cmd === "pair") reply = doPair(job);
      else if (job.cmd === "threshold") reply = doThreshold(job);
      else reply = { ok: false, cmd: job.cmd, error: "unknown command" };
    } catch (e) {
      if (e && e.mcRefusal)
        reply = { ok: false, cmd: job.cmd, refusal: e.mcRefusal };
      else
        reply = { ok: false, cmd: job.cmd,
                  error: (e && e.message) ? e.message : String(e) };
    }
    post(reply);
  };
  if (needsGk) gkEnsure(run); else run();
}

if (typeof self !== "undefined") self.onmessage = function (ev) { handle(ev.data); };

// the node verification harness loads this file directly
if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    handle: handle, groundPool: groundPool, groundClausified: groundClausified,
    parseClauseExport: parseClauseExport, questionFromGoal: questionFromGoal,
    questionInstances: questionInstances, questionVarOrder: questionVarOrder,
    thresholdEvaluate: thresholdEvaluate,
    queryAtomSign: queryAtomSign, wilson: wilson, pairedDiffCi: pairedDiffCi,
    sampleWorld: sampleWorld, worldDoc: worldDoc, REFUSE: REFUSE
  };
}
