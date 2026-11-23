// mcref_check.js: checks mcref.js, the JavaScript port of mcref 1.3.1,
// against the values of the Python tool mcref.py 1.3.1.
//
// The Python tool is published in https://github.com/tammet/gkreasoner
// (folder mcref/). The semantics is Doc/support_semantics.md there.
//
// Usage:
//   node mcref_check.js [--sets cases,page,generated,sampling] [--data FILE]
//                       [--only NAME] [--worlds N] [--from K] [--to M]
//
// The data file (default mcref_check_data.json.gz beside this file) holds
// the inputs and the reference values: the output of
// `mcref.py INPUT --mode exact` and of `mcref.py INPUT --mode exact
// --all-atoms`, with gk 1.3.2 as the tool's parser. Its sets:
//   cases      the 151 acceptance cases of the Python tool (its tests/
//              folder), each input with the options of its case and with
//              --all-atoms;
//   page       the examples of commonsense.html beside this file, as the
//              page passes them to the tool (a JSON example as written,
//              any other example converted by gk);
//   generated  2,000 generated inputs, drawn with a fixed seed from the
//              inputs of the experiments that compared gk with the tool,
//              with --all-atoms; two of them are the inputs whose value
//              changed from mcref 1.3.0 to 1.3.1;
//   sampling   the sampling of the port (--mode sampling, seed 1, N worlds,
//              default 20000): (a) on the page examples and on every tenth
//              generated input, the counts must equal the counts of
//              `mcref.py INPUT --mode sampling --samples 20000 --seed 1`;
//              (b) on every generated input with an exact value, every
//              sampled share (the four shares and the share without a
//              value, of every atom) must lie within the stated bound
//              (error_bound) of the exact share, and a share that is
//              exactly 0 or 1 must be sampled as 0 or 1; the check counts
//              the other shares that lie more than three standard errors
//              sqrt(p(1 - p)/N) from the exact share p, and the number that
//              chance alone gives, 0.0027 per share.
// An input that is not JSON is converted as the page converts it: by the
// WebAssembly build gkjs.js beside this file, `gk input -writejson
// -recursive`, in child processes.
//
// A run agrees when the port and the Python tool decline the input with the
// same reason, or both stop at the cell limit with the same message, or
// both give the same answers and atoms with each of the five numbers (for,
// against, conflict, ignorance and the share without a value) equal within
// 1e-9. The check prints every run that differs and the counts per set,
// and ends with exit status 1 when a run differs.

"use strict";

const fs = require("fs");
const path = require("path");
const zlib = require("zlib");
const cp = require("child_process");
const crypto = require("crypto");

const DIR = __dirname;
const GKJS = path.join(DIR, "gkjs.js");
const TOL = 1e-9;

// ---- child mode: convert a batch of inputs with the wasm build ----------------------------------------------------
// node mcref_check.js --convert FILE: FILE holds [{file, text}]; for each one the output of gk, between markers.

if (process.argv[2] === "--convert") {
  const batch = JSON.parse(fs.readFileSync(process.argv[3], "utf8"));
  process.argv = [process.argv[0], GKJS, "-version"];
  const M = require(GKJS);
  M.postRun = [function () {
    batch.forEach((b, k) => {
      process.stdout.write("\n===BEGIN " + k + "===\n");
      try {
        M.FS.writeFile(b.file, b.text);
        // Emscripten's callMain changes its argument array: each call gets a copy
        M.callMain([b.file, "-writejson", "-recursive"].slice());
      } catch (e) {
        if (!(e && e.name === "ExitStatus")) process.stdout.write("[exception] " + e + "\n");
      }
      process.stdout.write("\n===END " + k + "===\n");
    });
  }];
  return;
}

// ---- options ------------------------------------------------------------------------------------------------------

function parseArgs(argv) {
  const a = {sets: new Set(["cases", "page", "generated", "sampling"]), data: path.join(DIR, "mcref_check_data.json.gz"),
    only: null, worlds: 20000, from: 0, to: Infinity};
  for (let i = 0; i < argv.length; i++) {
    const k = argv[i];
    if (k === "--sets") a.sets = new Set(argv[++i].split(","));
    else if (k === "--data") a.data = argv[++i];
    else if (k === "--only") a.only = argv[++i];
    else if (k === "--worlds") a.worlds = parseInt(argv[++i], 10);
    else if (k === "--from") a.from = parseInt(argv[++i], 10);
    else if (k === "--to") a.to = parseInt(argv[++i], 10);
    else { console.error("unknown option " + k + "; see the comment at the top"); process.exit(2); }
  }
  return a;
}

// ---- conversion -------------------------------------------------------------------------------------------------

// conversions: [{file, text}] -> the outputs of gk, 50 to a child process
function convertAll(items) {
  const out = new Array(items.length);
  for (let s = 0; s < items.length; s += 50) {
    const part = items.slice(s, s + 50);
    const tmp = path.join(require("os").tmpdir(), "mcref_check_" + process.pid + "_" + s + ".json");
    fs.writeFileSync(tmp, JSON.stringify(part));
    const r = cp.spawnSync(process.execPath, [__filename, "--convert", tmp],
      {encoding: "utf8", maxBuffer: 1 << 30, timeout: 1800000});
    fs.unlinkSync(tmp);
    const text = r.stdout || "";
    part.forEach((p, k) => {
      const b = text.indexOf("\n===BEGIN " + k + "===\n"), e = text.indexOf("\n===END " + k + "===\n");
      out[s + k] = (b >= 0 && e > b) ? text.slice(b + ("\n===BEGIN " + k + "===\n").length, e) :
        "[conversion failed] " + (r.stderr || "").slice(-300);
    });
  }
  return out;
}

// ---- comparison -------------------------------------------------------------------------------------------------

function close(x, y) {
  if (!x || !y) return x === y;
  for (let k = 0; k < 4; k++) if (!(Math.abs(x[k] - y[k]) <= TOL)) return false;
  return true;
}

// the differences between the Python tool's output py and the port's js
function compare(py, js) {
  const d = [];
  if ((py.unsupported || null) !== (js.unsupported || null))
    d.push("declined: " + JSON.stringify(py.unsupported) + " / " + JSON.stringify(js.unsupported));
  if ((py.too_many_cells || null) !== (js.too_many_cells || null))
    d.push("cell limit: " + JSON.stringify(py.too_many_cells) + " / " + JSON.stringify(js.too_many_cells));
  const pa = py.answers || [], ja = js.answers || [];
  if (pa.length !== ja.length) d.push("answers: " + pa.length + " / " + ja.length);
  for (let i = 0; i < Math.min(pa.length, ja.length); i++) {
    if (pa[i].instance !== ja[i].instance) d.push("answer " + i + ": " + pa[i].instance + " / " + ja[i].instance);
    else if (!close(pa[i].value, ja[i].value) || !(Math.abs(pa[i].unstable - ja[i].unstable) <= TOL))
      d.push(pa[i].instance + ": " + JSON.stringify([pa[i].value, pa[i].unstable]) + " / " +
        JSON.stringify([ja[i].value, ja[i].unstable]));
  }
  const pv = py.atom_values || null, jv = js.atom_values || null;
  if (pv || jv) {
    if (!pv || !jv || pv.length !== jv.length) d.push("atoms: " + (pv ? pv.length : "none") + " / " + (jv ? jv.length : "none"));
    else {
      for (let i = 0; i < pv.length; i++) {
        const x = pv[i], y = jv[i];
        let ok = x.atom === y.atom;
        if (ok && x.unsupported !== undefined) ok = x.unsupported === y.unsupported;
        else if (ok) ok = close(x.value, y.value) && Math.abs(x.unstable - y.unstable) <= TOL;
        if (!ok) d.push("atom " + JSON.stringify(x) + " / " + JSON.stringify(y));
      }
    }
  }
  return d;
}

// the counts of a sampled run against the Python tool's counts: equal
function compareCounts(py, js) {
  const d = [];
  if ((py.unsupported || null) !== (js.unsupported || null))
    d.push("declined: " + JSON.stringify(py.unsupported) + " / " + JSON.stringify(js.unsupported));
  const pa = py.answers || [], ja = js.answers || [];
  if (pa.length !== ja.length) d.push("answers: " + pa.length + " / " + ja.length);
  for (let i = 0; i < Math.min(pa.length, ja.length); i++) {
    if (pa[i].instance !== ja[i].instance || JSON.stringify(pa[i].counts) !== JSON.stringify(ja[i].counts))
      d.push(pa[i].instance + ": counts " + JSON.stringify(pa[i].counts) + " / " + JSON.stringify(ja[i].counts));
  }
  const pv = py.atom_values || [], jv = js.atom_values || [];
  if (pv.length !== jv.length) d.push("atoms: " + pv.length + " / " + jv.length);
  else for (let i = 0; i < pv.length; i++) {
    if (pv[i].atom !== jv[i].atom || JSON.stringify(pv[i].counts) !== JSON.stringify(jv[i].counts))
      d.push("atom " + pv[i].atom + ": counts " + JSON.stringify(pv[i].counts) + " / " + JSON.stringify(jv[i].counts));
  }
  return d;
}

// a sampled run against the exact values: the stated bound, the shares that are exactly 0 or 1, three standard
// errors
function checkBound(ex, js, b) {
  const d = [];
  if (js.mode !== "sampling") return ["the run did not sample"];
  const n = js.worlds, e = js.error_bound;
  const pv = ex.atom_values || [], jv = js.atom_values || [];
  if (pv.length !== jv.length) return ["atoms: " + pv.length + " / " + jv.length];
  b.runs++;
  for (let i = 0; i < pv.length; i++) {
    if (pv[i].atom !== jv[i].atom) { d.push("atom " + pv[i].atom + " / " + jv[i].atom); continue; }
    if (pv[i].unsupported !== undefined) continue;
    const xs = pv[i].value.concat([pv[i].unstable]), ys = jv[i].value.concat([jv[i].unstable]);
    for (let k = 0; k < 5; k++) {
      const p = xs[k], s = ys[k];
      b.shares++;
      if (Math.abs(p) <= 1e-12 || Math.abs(p - 1) <= 1e-12) {
        b.zeroOne++;
        if (Math.abs(s - p) > 1e-12) { b.zeroOneBad++; d.push(pv[i].atom + " share " + k + ": exact " + p + ", sampled " + s); }
        continue;
      }
      const dist = Math.abs(s - p);
      if (dist > e + 1e-12) { b.outside++; d.push(pv[i].atom + " share " + k + ": exact " + p + ", sampled " + s + ", bound " + e); }
      b.worst = Math.max(b.worst, dist / e);
      const se = Math.sqrt(p * (1 - p) / n);
      if (dist > 3 * se) b.beyond3++;
      b.expected3 += 0.0027;
    }
  }
  return d;
}

// ---- the page examples ----------------------------------------------------------------------------------------------

function pageExamples() {
  const html = fs.readFileSync(path.join(DIR, "commonsense.html"), "utf8");
  const re = /<code id="example_cs(\d+)_input_code">([\s\S]*?)<\/code>/g;
  const out = new Map();
  let m;
  while ((m = re.exec(html))) out.set(m[1], m[2].replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&"));
  return out;
}

// ---- main -----------------------------------------------------------------------------------------------------------

function main() {
  const a = parseArgs(process.argv.slice(2));
  const {mcref, VERSION} = require(path.join(DIR, "mcref.js"));
  const data = JSON.parse(zlib.gunzipSync(fs.readFileSync(a.data)).toString("utf8"));
  // --from and --to select the generated inputs K to M - 1 (for a check in parts)
  data.generated = data.generated.slice(a.from, Math.min(a.to, data.generated.length));
  console.log("mcref.js " + VERSION + " against " + data.reference);
  // the runs: {set, name, text, file (for gk), json (read as written), options, ref, cases}
  const runs = [];
  if (a.sets.has("cases")) {
    for (const e of data.cases) {
      for (const r of e.runs) runs.push({set: "cases", name: e.name + (r.options.length ? " " + r.options.join(" ") : ""),
        text: e.text, ext: e.ext, options: r.options, ref: r.ref, cases: e.cases});
    }
  }
  if (a.sets.has("page")) {
    const ex = pageExamples();
    for (const e of data.page) {
      const text = ex.get(e.id);
      const sha = text === undefined ? null : crypto.createHash("sha256").update(text).digest("hex");
      for (const r of e.runs) {
        runs.push({set: "page", name: "example " + e.id + (r.options.length ? " " + r.options.join(" ") : ""),
          text: text, page: true, changed: sha !== e.sha256, options: r.options, ref: r.ref});
      }
    }
  }
  if (a.sets.has("generated")) {
    for (const e of data.generated) runs.push({set: "generated", name: e.name + " (" + e.origin + ")", text: e.text,
      ext: e.ext, options: e.options, ref: e.ref});
  }
  if (a.sets.has("sampling")) {
    const ex = pageExamples();
    for (const e of data.page) {
      const text = ex.get(e.id);
      const sha = text === undefined ? null : crypto.createHash("sha256").update(text).digest("hex");
      for (const r of e.sampling || []) {
        runs.push({set: "sampling", kind: "counts", name: "example " + e.id + (r.options.length ? " " + r.options.join(" ") : "") +
          " sampled", text: text, page: true, changed: sha !== e.sha256, options: r.options, ref: r.ref, worlds: r.worlds});
      }
    }
    for (const e of data.generated) {
      if (e.sampling) runs.push({set: "sampling", kind: "counts", name: e.name + " sampled", text: e.text, ext: e.ext,
        options: e.options, ref: e.sampling.ref, worlds: e.sampling.worlds});
      if (!e.ref.unsupported && !e.ref.too_many_cells && e.ref.atom_values)
        runs.push({set: "sampling", kind: "bound", name: e.name + " bound", text: e.text, ext: e.ext, options: e.options,
          ref: e.ref, worlds: a.worlds});
    }
  }
  const todo = runs.filter(r => !a.only || r.name.indexOf(a.only) >= 0);
  // the conversions: a page example as the page converts it (the file "input"), any other input that is not JSON
  // under its own extension, as mcref.py converts it
  const conv = [], convOf = new Map();
  for (const r of todo) {
    if (r.changed || r.text === undefined) continue;
    if (!r.page && (r.ext === "js" || r.ext === "json")) continue;
    const file = r.page ? "input" : "input." + r.ext;
    const key = file + "\u0000" + r.text;
    if (!convOf.has(key)) { convOf.set(key, conv.length); conv.push({file: file, text: r.text}); }
    r.conv = convOf.get(key);
  }
  const t0 = Date.now();
  const outs = convertAll(conv);
  const tconv = (Date.now() - t0) / 1000;
  const counts = {};
  const bound = {shares: 0, zeroOne: 0, zeroOneBad: 0, outside: 0, beyond3: 0, expected3: 0, runs: 0, worst: 0};
  let ndiff = 0;
  const t1 = Date.now();
  for (const r of todo) {
    const c = counts[r.set] || (counts[r.set] = {runs: 0, agree: 0, differ: 0, cases: new Set(), caseFail: new Set()});
    c.runs++;
    let d;
    if (r.changed) d = ["the page example changed since the reference values were made"];
    else {
      const opts = {allAtoms: r.options.indexOf("--all-atoms") >= 0, name: r.name};
      let text = r.text;
      if (r.conv !== undefined) {
        const o = outs[r.conv];
        if (!(r.page && o.indexOf("passed through unchanged") >= 0)) {
          text = o;
          opts.convertedBy = "gk -writejson -recursive";
          opts.conversionOutput = o;
        }
      }
      // the reference values of the sets cases, page and generated come from --mode exact
      if (r.set === "sampling") { opts.mode = "sampling"; opts.samples = r.worlds; opts.seed = 1; }
      else opts.mode = "exact";
      try {
        const js = mcref(text, opts);
        d = r.kind === "counts" ? compareCounts(r.ref, js) : r.kind === "bound" ? checkBound(r.ref, js, bound) : compare(r.ref, js);
      } catch (e) { d = ["error: " + ((e && e.message) || e)]; }
    }
    if (d.length) {
      c.differ++;
      ndiff++;
      console.log("DIFFERS " + r.set + " " + r.name + ": " + d.slice(0, 5).join("; ") + (d.length > 5 ? "; ..." : ""));
      if (r.cases) r.cases.forEach(x => c.caseFail.add(x));
    } else c.agree++;
    if (r.cases) r.cases.forEach(x => c.cases.add(x));
  }
  const teval = (Date.now() - t1) / 1000;
  if (bound.runs) {
    console.log("sampling bound, " + a.worlds + " worlds, seed 1, on " + bound.runs + " generated inputs with an exact value: " +
      bound.shares + " shares; " + bound.outside + " outside the stated bound (largest distance in bounds " +
      bound.worst.toFixed(3) + "); " + bound.zeroOne + " exactly 0 or 1, " + bound.zeroOneBad + " of them sampled otherwise; " +
      "of the other " + (bound.shares - bound.zeroOne) + " shares " + bound.beyond3 + " lie more than three standard errors " +
      "from the exact share, where chance alone gives about " + bound.expected3.toFixed(1));
  }
  for (const s of Object.keys(counts)) {
    const c = counts[s];
    console.log(s + ": " + c.runs + " runs, " + c.agree + " agree, " + c.differ + " differ" +
      (c.cases.size ? "; " + c.cases.size + " cases, " + (c.cases.size - c.caseFail.size) + " agree" : ""));
  }
  console.log(conv.length + " conversions in " + tconv.toFixed(1) + " s; the port in " + teval.toFixed(1) + " s");
  console.log(ndiff ? ndiff + " run(s) differ" : "every run agrees");
  process.exit(ndiff ? 1 : 0);
}

main();
