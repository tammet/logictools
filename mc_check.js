// Verification harness for the sampling check (mcsampler.js), in the pattern
// of commonsense_check.js: it drives the SAME worker code that
// commonsense.html runs in the browser, through the same messages.
//
//   /opt/gkcjs/emsdk/node/12.18.1_64bit/bin/node mc_check.js           (all)
//   /opt/gkcjs/emsdk/node/12.18.1_64bit/bin/node mc_check.js 3 7 10    (some)
//   MC_TRIALS=300 ... mc_check.js                    (fewer worlds, quicker)
//
// One process = one solver instance, exactly as one Web Worker is on the
// page. When the worker hands a job back unfinished (see the retirement note
// in mcsampler.js), the parent starts a fresh process for the remainder, the
// same way the page starts a fresh worker. That keeps the retirement path
// under test rather than around it.
//
// The expectations are the reference values of the Python implementation in
// /opt/gkreasoner/montecarlo (gkmc.py at 4000 trials, threshold_worlds.py at
// 100000 draws, seed 1), NOT gk's own confidences: the point of sampling is
// to be an independent check, and it is expected to differ from gk on some
// examples. Inclusion estimates are compared by interval overlap, the four
// masses by absolute difference.

var fs = require("fs");
var path = require("path");
var os = require("os");
var child_process = require("child_process");

var DIR = __dirname;
var GKJS = path.join(DIR, "gkjs.js");
var PAGE = path.join(DIR, "commonsense.html");
var SAMPLER = path.join(DIR, "mcsampler.js");

var TRIALS = parseInt(process.env.MC_TRIALS || "1000", 10);  // reference: 4000
var THR_TRIALS = 100000;
var SEED = 0;

// ---- expectations ---------------------------------------------------------
// incl: the answers to check, with the Python pos-neg estimate where one
//   exists (mc_check_ref.json overrides these); null means "run it, no
//   number to match".
// thr: the Python four masses [for, against, conflict, ignorance].
// refuse / thrRefuse: the exact refusal the input must produce instead.
// gk: gk's own confidence per answer, checked against the reference run.

var EXAMPLES = {
  "1":  { incl: { "polly": 1.0 }, gk: { "polly": 1.0 } },
  "2":  { incl: { "yes": 0.56 }, thr: [0.56, 0, 0, 0.44], gk: { "yes": 0.56 } },
  "3":  { incl: { "yes": 0.80 }, thr: [0.80, 0, 0, 0.20], gk: { "yes": 0.8 } },
  "4":  { incl: { "yes": 0.30 }, thr: [0.30, 0, 0.40, 0.30], gk: { "yes": 0.3 } },
  "5":  { incl: { "yes": null }, thr: null },
  "6":  { incl: { "yes": null }, thr: null },
  "7":  { incl: { "yes": null }, thr: null, gk: { "yes": 0.27 } },
  "8":  { incl: { "tweety": 1.0, "robin": 1.0 } },
  "9":  { incl: { "robin": 1.0, "tweety": null } },
  // ex10: gk reports the penguin as a rejected answer; no world proves it,
  // since the blocked default cannot fire. ex11 is the Nixon standoff: gk
  // commits to neither side and no world proves the answer either.
  "10": { incl: { "tweety": 1.0 }, gk: { "tweety": 1.0, "pingu": 1.0 } },
  "11": { incl: {}, gk: { "nixon": 0.0 } },
  // ex12 (where is John) is eligible, but its grounding is ~20000 clauses
  // and each sampled world takes about a second: only its setup verdict and
  // the four-mass refusal (open query) are checked here
  "12": { skipIncl: true, thrRefuse: "thrOpen" },
  "13": { refuse: "builtin" },
  "14": { refuse: "builtin" },
  "15": { incl: { "tweety": null } },
  "16": { incl: { "yes": 0.56 }, thr: [0.56, 0, 0, 0.44], gk: { "yes": 0.56 } },
  "17": { incl: { "yes": 0.56 }, thr: [0.56, 0, 0, 0.44], gk: { "yes": 0.56 } },
  // ex18 asks which bird does NOT fly: gk rejects p (0.08 against), while
  // sampling counts the worlds in which -flies(p) is provable (about 0.64)
  "18": { incl: { "p": null }, gk: { "p": 0.08 } },
  "19": { incl: { "yes": 1.0 }, thr: [1.0, 0, 0, 0] },
  "20": { refuse: "functions" },
  // the page refuses ex23 before the worker sees it (its preset loads the
  // taxonomy); here only its four-mass verdict is checked. Its query has a
  // variable, which is found before its named blocker priorities.
  "23": { skipIncl: true, thrRefuse: "thrOpen" }
};

var REFFILE = path.join(DIR, "mc_check_ref.json");
var REF = fs.existsSync(REFFILE)
  ? JSON.parse(fs.readFileSync(REFFILE, "utf8")) : {};

// ---- reading the page's examples (same unescaping selectExample does) -----

function readInput(id) {
  var page = fs.readFileSync(PAGE, "utf8");
  var re = new RegExp('<code id="example_cs' + id + '_input_code">([\\s\\S]*?)</code>');
  var m = page.match(re);
  if (!m) throw new Error("example " + id + " not found in commonsense.html");
  return m[1]
    .replace(/&amp;/g, "&")
    .replace(/&gt;/g, ">")
    .replace(/&lt;/g, "<");
}

// ==========================================================================
// worker mode: one process, one solver instance, one job
//   --job <file>   the job to run, as JSON; the reply is written back to it
// ==========================================================================

if (process.argv[2] === "--job") {
  var jobFile = process.argv[3];
  var job = JSON.parse(fs.readFileSync(jobFile, "utf8"));

  // The node build of the emscripten glue ignores a preset Module.print, so
  // the harness supplies its own adapter (self.MC_HOST) and captures stdout.
  // It also turns gk's exit() into process.exit(), which would kill this
  // process without a word, so that is turned back into a throw.
  var M = null;
  var captured = "";
  var realWrite = process.stdout.write.bind(process.stdout);
  var realExit = process.exit.bind(process);

  global.self = global;
  global.self.MC_HOST = {
    init: function (cb) {
      if (M) { cb(); return; }
      process.argv = [process.argv[0], GKJS, "-version"];
      M = require(GKJS);
      M.postRun = [function () { cb(); }];
    },
    run: function (files, args) {
      for (var i = 0; i < files.length; i++)
        M.FS.writeFile(files[i].name, files[i].data);
      captured = "";
      process.stdout.write = function (s) { captured += s; return true; };
      process.exit = function (code) { throw new Error("gk exited " + code); };
      try { M.callMain(args); } catch (e) { /* ExitStatus, or the above */ }
      process.exit = realExit;
      process.stdout.write = realWrite;
      return captured;
    }
  };

  global.self.postMessage = function (msg) {
    if (msg && msg.progress) return;
    fs.writeFileSync(jobFile + ".reply", JSON.stringify(msg));
    realExit(0);
  };

  require(SAMPLER);
  global.self.onmessage({ data: job });
  return;
}

// ==========================================================================
// parent mode
// ==========================================================================

var sampler = require(SAMPLER);
var TMP = fs.mkdtempSync(path.join(os.tmpdir(), "mccheck_"));

// Run one job in a fresh process and return its reply.
function ask(job) {
  var f = path.join(TMP, "job.json");
  fs.writeFileSync(f, JSON.stringify(job));
  try { fs.unlinkSync(f + ".reply"); } catch (e) {}
  var r = child_process.spawnSync(process.execPath, [__filename, "--job", f],
                                  { encoding: "utf8", timeout: 900000,
                                    maxBuffer: 64 * 1024 * 1024 });
  if (!fs.existsSync(f + ".reply"))
    return { ok: false, error: "worker produced no reply: " +
             ((r.stderr || r.stdout || "").slice(-300)) };
  return JSON.parse(fs.readFileSync(f + ".reply", "utf8"));
}

// Run a job to completion, restarting on retirement exactly as the page does.
function askAll(job, onPartial) {
  for (var guard = 0; guard < 10000; guard++) {
    var r = ask(job);
    if (!r.ok || !r.retire) return r;
    onPartial(r, job);
  }
  throw new Error("job never finished");
}

function runExample(id) {
  var input = readInput(id);
  var out = { id: id, restarts: 0 };

  // setup: ask for the four-mass pool first, and fall back to an inclusion
  // setup when the input is outside that narrower fragment (as the page does
  // when the method menu is not on "four masses")
  var setup = ask({ cmd: "setup", input: input, seconds: 5, method: "threshold" });
  var thrSetup = setup;
  if (!setup.ok && setup.refusal)
    setup = ask({ cmd: "setup", input: input, seconds: 5, method: "subtract" });
  if (!setup.ok) {
    out.refusal = setup.refusal || null;
    out.error = setup.error || null;
    return out;
  }
  out.reference = setup.reference;
  out.warnings = setup.warnings;
  out.poolSize = setup.pool.length;
  out.questions = setup.questions;

  if (thrSetup.ok && thrSetup.thresholdPool) {
    out.threshold = ask({ cmd: "threshold", pool: thrSetup.thresholdPool,
                          queryAtom: thrSetup.queryAtom,
                          querySign: thrSetup.querySign,
                          trials: THR_TRIALS, seed: SEED });
  } else {
    out.thresholdRefusal = thrSetup.refusal || null;
  }
  if (EXAMPLES[id] && EXAMPLES[id].skipIncl) return out;

  // phase 1: the sampled worlds
  var keys = new Array(TRIALS), values = {}, invalid = 0;
  var res = askAll({ cmd: "trials", pool: setup.pool, questions: setup.questions,
                     draws: "per-instance", seed: SEED, from: 0, to: TRIALS },
    function (partial, job) {
      collectTrials(partial);
      job.from = partial.to;
      out.restarts++;
    });
  if (!res.ok) { out.error = res.error || res.refusal; return out; }
  collectTrials(res);

  function collectTrials(r) {
    for (var i = 0; i < r.keys.length; i++) keys[r.from + i] = r.keys[i];
    for (var k in r.values) if (r.values.hasOwnProperty(k)) {
      if (!values.hasOwnProperty(k)) values[k] = r.values[k];
    }
    invalid += r.invalid;
  }

  // keys[i] is null for a world that could not be decided and [] for one
  // decided with no answer: the second is a valid world, the first is not
  var counts = {}, valid = [];
  for (var i = 0; i < keys.length; i++) {
    if (keys[i] === undefined) { invalid++; continue; }   // never assigned
    if (keys[i] === null) continue;
    valid.push(i);
    for (var j = 0; j < keys[i].length; j++)
      counts[keys[i][j]] = (counts[keys[i][j]] || 0) + 1;
  }
  out.counts = counts;
  out.valid = valid.length;
  out.invalid = invalid;
  out.values = values;

  // phase 2: the per-answer pairing pass
  out.pairs = {};
  var qs = setup.questions[0];
  var answers = Object.keys(counts);
  for (var ai = 0; ai < answers.length; ai++) {
    var key = answers[ai];
    var vals = (key === "yes") ? [] : (values[key] || []);
    var posKnown = [];
    for (i = 0; i < valid.length; i++)
      posKnown.push(keys[valid[i]].indexOf(key) >= 0);
    var cells = { pos_only: 0, neg_only: 0, both: 0, neither: 0 }, n = 0;
    var warning = null;
    var pr = askAll({ cmd: "pair", pool: setup.pool, draws: "per-instance",
                      seed: SEED, question: qs, values: vals, answer: key,
                      trials: valid.slice(), posKnown: posKnown },
      function (partial, job) {
        addCells(partial);
        job.trials = job.trials.slice(partial.consumed);
        job.posKnown = job.posKnown.slice(partial.consumed);
        out.restarts++;
      });
    if (!pr.ok) { out.error = pr.error || pr.refusal; return out; }
    addCells(pr);
    out.pairs[key] = { cells: cells, n: n, warning: warning };

    function addCells(r) {
      if (r.warning) warning = r.warning;
      if (!r.cells) return;
      for (var c in r.cells) if (r.cells.hasOwnProperty(c)) cells[c] += r.cells[c];
      n += r.n;
    }
  }
  return out;
}

// ---- checking -------------------------------------------------------------

var ids = process.argv.slice(2);
if (!ids.length) ids = Object.keys(EXAMPLES);

var pass = 0, fail = 0;
var failures = [];

function ok(id, what) { pass++; console.log("OK    ex" + id + "  " + what); }
function bad(id, what) {
  fail++; failures.push("ex" + id + ": " + what);
  console.log("FAIL  ex" + id + "  " + what);
}

for (var ii = 0; ii < ids.length; ii++) {
  var id = ids[ii];
  var spec = EXAMPLES[id];
  if (!spec) { console.log("skip  ex" + id + " (no expectations)"); continue; }
  var t0 = Date.now();
  var out;
  try { out = runExample(id); }
  catch (e) { bad(id, "harness error: " + (e && e.message ? e.message : e)); continue; }
  var secs = ((Date.now() - t0) / 1000).toFixed(1);

  if (spec.refuse) {
    var want = sampler.REFUSE[spec.refuse];
    if (out.refusal === want) ok(id, "refused: " + want.slice(0, 46) + "...");
    else bad(id, "expected refusal '" + spec.refuse + "' (" + want + "), got " +
             (out.refusal ? "'" + out.refusal + "'" :
              (out.error ? "error " + out.error : "a successful run")));
    continue;
  }
  if (out.refusal) { bad(id, "unexpected refusal: " + out.refusal); continue; }
  if (out.error) { bad(id, "error: " + out.error); continue; }

  var problems = [];
  var report = [];

  if (spec.thrRefuse) {
    var twant = sampler.REFUSE[spec.thrRefuse];
    if (out.thresholdRefusal === twant)
      report.push("four masses refused as expected");
    else
      problems.push("expected the four-mass refusal '" + spec.thrRefuse +
                    "', got " + (out.thresholdRefusal
                      ? "'" + out.thresholdRefusal + "'" : "a scored run"));
  }

  // --- inclusion: interval overlap with the Python reference
  var incl = spec.incl || {};
  var refIncl = (REF[id] && REF[id].incl) || {};
  if (!spec.skipIncl) {
    for (var key2 in incl) if (incl.hasOwnProperty(key2)) {
      var pr2 = out.pairs[key2];
      if (!pr2 || !pr2.n) { problems.push("answer '" + key2 + "' never sampled"); continue; }
      var ci = sampler.pairedDiffCi(pr2.cells.pos_only, pr2.cells.neg_only, pr2.n);
      report.push(key2 + "=" + ci.diff.toFixed(3));
      var want2 = (refIncl[key2] !== undefined) ? refIncl[key2] : incl[key2];
      if (want2 === null || want2 === undefined) continue;
      // the JS interval must cover the reference point, allowing for the
      // reference's own 4000-trial half width (~0.016) and rounding
      var margin = 0.02;
      if (ci.hi < want2 - margin || ci.lo > want2 + margin)
        problems.push("answer '" + key2 + "': sampled " + ci.diff.toFixed(3) +
                      " [" + ci.lo.toFixed(3) + ", " + ci.hi.toFixed(3) +
                      "] does not cover the reference " + want2);
    }
    for (var k3 in out.pairs) if (out.pairs.hasOwnProperty(k3)) {
      if (!incl.hasOwnProperty(k3) && !refIncl.hasOwnProperty(k3))
        problems.push("unexpected sampled answer '" + k3 + "'");
    }
  }

  // --- four masses
  var refThr = (REF[id] && REF[id].thr) || spec.thr;
  var scored = out.threshold && out.threshold.ok && !out.threshold.notScored;
  if (out.threshold && out.threshold.notScored)
    report.push("masses not scored (" + out.threshold.notScored + ")");
  if (refThr && (spec.thr || spec.thr === null)) {
    if (!scored && spec.thr) {
      problems.push("four masses not produced: " +
                    (out.thresholdRefusal ||
                     (out.threshold && out.threshold.notScored) || "no result"));
    } else if (scored) {
      var got = [out.threshold.support_for, out.threshold.support_against,
                 out.threshold.conflict, out.threshold.ignorance];
      report.push("masses=" + got.map(function (x) { return x.toFixed(3); }).join("/"));
      for (var f = 0; f < 4; f++)
        if (Math.abs(got[f] - refThr[f]) > 0.01)
          problems.push("mass " + f + ": got " + got[f].toFixed(4) +
                        " expected " + refThr[f]);
    }
  }

  // --- gk's own numbers, as parsed from the reference run
  if (spec.gk) {
    for (var gkey in spec.gk) if (spec.gk.hasOwnProperty(gkey)) {
      var a = out.reference && out.reference.answers[gkey];
      if (!a) problems.push("gk reported no answer '" + gkey + "'");
      else if (Math.abs(a.confidence - spec.gk[gkey]) > 0.005)
        problems.push("gk confidence for '" + gkey + "': got " + a.confidence +
                      " expected " + spec.gk[gkey]);
    }
  }

  var timing = "(" + secs + "s, pool " + out.poolSize +
               (out.valid !== undefined ? ", " + out.valid + " valid worlds" : "") +
               (out.restarts ? ", " + out.restarts + " solver restarts" : "") + ")";
  if (problems.length) bad(id, problems.join("; ") + " " + timing);
  else ok(id, report.join(" ") + " " + timing);
}

console.log("\n" + pass + " pass, " + fail + " fail");
if (failures.length) {
  console.log("\nfailures:");
  for (var fi = 0; fi < failures.length; fi++) console.log("  " + failures[fi]);
}
try { fs.readdirSync(TMP).forEach(function (f) { fs.unlinkSync(path.join(TMP, f)); });
      fs.rmdirSync(TMP); } catch (e) {}
process.exit(fail ? 1 : 0);
