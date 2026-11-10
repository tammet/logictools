// mcref_check.js: compares mcref.js, the JavaScript port of mcref 1.1.1, with
// the Python tool mcref.py on the same inputs, seed and sample count.
//
// The Python tool is published in https://github.com/tammet/gkreasoner. The
// semantics is Doc/support_semantics.md of the gk repository.
//
// Usage:
//   node mcref_check.js --gk-repo DIR --out DIR [options]
//
// --gk-repo DIR      a gk checkout with the gk binary at its top; it sets the
//                    defaults of --mcref, --gk, --semantics and --cases
// --mcref FILE       mcref.py
// --gk FILE          the gk binary; it converts the inputs that are not JSON,
//                    for the port and (through MCREF_GK) for mcref.py
// --semantics DIR    a folder of inputs, every file except README.md
// --cases DIR        the acceptance tests of mcref: step*/expected*.json
// --page-inputs DIR  the page examples as ex1.txt, ex2.txt, ...; without it,
//                    the examples of commonsense.html next to this file
// --out DIR          the folder for the results
// --samples N        the samples for the semantics inputs and page examples
//                    (default 100000); an acceptance case uses its own
// --sets LIST        any of semantics,cases,page (default all three)
// --jobs N           the mcref.py processes at a time (default 6)
// --python CMD       the Python interpreter (default python3)
//
// For an input that is not JSON, the harness runs `gk FILE -writejson
// -recursive` in the file's folder, as mcref.py does, and gives the output
// to the port. A page example without a file extension is converted the
// same way; when its text is JSON, the harness also runs both tools on the
// text itself (the name ends with "(json)").
//
// The harness writes results.json and summary.md, and the two tools' results
// in native/ and port/. It reports for each run: the same unsupported
// reason or not; per answer, the counts of both tools and whether they are
// identical; when they differ, whether every share differs by at most
// e = sqrt(ln(8/.05)/(2N)); whether the two whole results are equal except
// version, input and provenance; and the times.

"use strict";

const fs = require("fs");
const path = require("path");
const cp = require("child_process");
const {mcref, sha256} = require("./mcref.js");

function parseArgs(argv) {
  const a = {jobs: 6, samples: 100000, sets: "semantics,cases,page", python: "python3"};
  for (let i = 0; i < argv.length; i++) {
    const k = argv[i];
    const take = () => argv[++i];
    if (k === "--gk-repo") a.gkRepo = take();
    else if (k === "--mcref") a.mcref = take();
    else if (k === "--gk") a.gk = take();
    else if (k === "--semantics") a.semantics = take();
    else if (k === "--cases") a.cases = take();
    else if (k === "--page-inputs") a.pageInputs = take();
    else if (k === "--out") a.out = take();
    else if (k === "--samples") a.samples = parseInt(take(), 10);
    else if (k === "--sets") a.sets = take();
    else if (k === "--jobs") a.jobs = parseInt(take(), 10);
    else if (k === "--python") a.python = take();
    else { console.error("unknown option " + k); process.exit(2); }
  }
  if (a.gkRepo) {
    const r = path.resolve(a.gkRepo);
    a.mcref = a.mcref || path.join(r, "experiments", "mc_reference", "mcref.py");
    a.gk = a.gk || path.join(r, "gk");
    a.semantics = a.semantics || path.join(r, "Examples", "semantics");
    a.cases = a.cases || path.join(r, "experiments", "mc_reference", "tests");
  }
  if (!a.mcref || !a.gk || !a.out) {
    console.error("usage: node mcref_check.js --gk-repo DIR --out DIR [options]; see the comment at the top");
    process.exit(2);
  }
  a.sets = new Set(a.sets.split(","));
  return a;
}

function hoeffding(n) { return Math.sqrt(Math.log(8 / 0.05) / (2 * n)); }

// the page examples of commonsense.html, as commonsense_check.js reads them
function pageExamples(dir) {
  const out = [];
  if (dir) {
    const names = fs.readdirSync(dir).filter(f => /^ex\d+\.txt$/.test(f));
    names.sort((x, y) => parseInt(x.slice(2), 10) - parseInt(y.slice(2), 10));
    for (const f of names) out.push({id: f.slice(0, -4), text: fs.readFileSync(path.join(dir, f), "utf8")});
    return out;
  }
  const html = fs.readFileSync(path.join(__dirname, "commonsense.html"), "utf8");
  const re = /<code id="example_cs(\d+)_input_code">([\s\S]*?)<\/code>/g;
  let m;
  while ((m = re.exec(html))) {
    const text = m[2].replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
    out.push({id: "ex" + m[1], text: text});
  }
  return out;
}

// the runs: {name, set, file, samples, options, viaGk}
function collectRuns(a) {
  const runs = [];
  if (a.sets.has("semantics") && a.semantics) {
    for (const f of fs.readdirSync(a.semantics).sort()) {
      if (f === "README.md") continue;
      const p = path.join(a.semantics, f);
      if (!fs.statSync(p).isFile()) continue;
      runs.push({name: "semantics/" + f, set: "semantics", file: p, samples: a.samples, options: []});
    }
  }
  if (a.sets.has("cases") && a.cases) {
    const byKey = new Map();
    const steps = fs.readdirSync(a.cases).filter(d => /^step/.test(d)).sort();
    for (const d of steps) {
      for (const f of fs.readdirSync(path.join(a.cases, d)).filter(x => /^expected.*\.json$/.test(x)).sort()) {
        const ef = path.join(a.cases, d, f);
        const e = JSON.parse(fs.readFileSync(ef, "utf8"));
        const cases = Array.isArray(e) ? e : e.cases;
        if (!Array.isArray(cases)) continue;   // a record of changes, not of cases
        for (const c of cases) {
          const p = path.normalize(path.join(path.dirname(ef), c.input));
          const opts = c.options || [];
          const ns = c.samples || e.samples || 100000;
          const key = p + "|" + ns + "|" + opts.join(" ");
          if (!byKey.has(key)) {
            const r = {name: "cases/" + path.relative(a.cases, p) + (opts.length ? " " + opts.join(" ") : "") +
              " N=" + ns, set: "cases", file: p, samples: ns, options: opts, cases: []};
            byKey.set(key, r);
            runs.push(r);
          }
          byKey.get(key).cases.push(d + "/" + c.case);
        }
      }
    }
  }
  if (a.sets.has("page")) {
    const base = path.join(a.out, "page_inputs");
    for (const ex of pageExamples(a.pageInputs)) {
      const d = path.join(base, ex.id);
      fs.mkdirSync(d, {recursive: true});
      const f = path.join(d, "input");
      fs.writeFileSync(f, ex.text);
      runs.push({name: "page/" + ex.id, set: "page", file: f, samples: a.samples, options: []});
      const {_internals} = require("./mcref.js");
      if (_internals.stripComments(ex.text).trim().startsWith("[")) {
        const fj = path.join(d, "input.js");
        fs.writeFileSync(fj, ex.text);
        runs.push({name: "page/" + ex.id + " (json)", set: "page", file: fj, samples: a.samples, options: []});
      }
    }
  }
  return runs;
}

// gk's conversion, as mcref_read.py runs it
function convert(a, file) {
  const t0 = process.hrtime.bigint();
  const p = cp.spawnSync(a.gk, [path.basename(file), "-writejson", "-recursive"],
    {cwd: path.dirname(path.resolve(file)), encoding: "utf8", timeout: 120000, maxBuffer: 1 << 30,
      killSignal: "SIGKILL"});
  const secs = Number(process.hrtime.bigint() - t0) / 1e9;
  return {stdout: p.stdout || "", output: (p.stdout || "") + (p.stderr || ""), secs: secs,
    timeout: !!(p.error && p.error.code === "ETIMEDOUT")};
}

// one mcref.py run in its own process group; the group is killed on timeout
function runNative(a, r) {
  return new Promise(resolve => {
    const args = ["-I", a.mcref, r.file, "--samples", String(r.samples), "--seed", "1"].concat(r.options);
    const t0 = process.hrtime.bigint();
    const env = Object.assign({}, process.env, {MCREF_GK: path.resolve(a.gk)});
    const ch = cp.spawn(a.python, args, {detached: true, env: env, stdio: ["ignore", "pipe", "pipe"]});
    let out = "", err = "";
    ch.stdout.on("data", d => { out += d; });
    ch.stderr.on("data", d => { err += d; });
    const timer = setTimeout(() => { try { process.kill(-ch.pid, "SIGKILL"); } catch (e) { /* gone */ } }, 3600 * 1000);
    ch.on("close", code => {
      clearTimeout(timer);
      const secs = Number(process.hrtime.bigint() - t0) / 1e9;
      let res = null;
      const line = out.split("\n").find(l => l.startsWith('{"mcref"'));
      if (line) { try { res = JSON.parse(line).mcref; } catch (e) { res = null; } }
      resolve({res: res, code: code, err: err.slice(-2000), secs: secs});
    });
  });
}

async function pool(items, jobs, fn) {
  let next = 0;
  const workers = [];
  for (let w = 0; w < jobs; w++) {
    workers.push((async () => {
      while (next < items.length) {
        const i = next++;
        await fn(items[i], i);
      }
    })());
  }
  await Promise.all(workers);
}

// the first path where two JSON values differ, or null
function firstDiff(x, y, p) {
  if (x === y) return null;
  if (typeof x === "number" && typeof y === "number") {
    if (x !== x && y !== y) return null;
    return p;
  }
  if (Array.isArray(x) && Array.isArray(y)) {
    if (x.length !== y.length) return p + ".length";
    for (let i = 0; i < x.length; i++) {
      const d = firstDiff(x[i], y[i], p + "[" + i + "]");
      if (d) return d;
    }
    return null;
  }
  if (x && y && typeof x === "object" && typeof y === "object" && !Array.isArray(x) && !Array.isArray(y)) {
    const kx = Object.keys(x), ky = Object.keys(y);
    if (kx.join("\u0000") !== ky.join("\u0000")) return p + " (keys " + kx.join(",") + " / " + ky.join(",") + ")";
    for (const k of kx) {
      const d = firstDiff(x[k], y[k], p + "." + k);
      if (d) return d;
    }
    return null;
  }
  return p;
}

function comparable(r) {
  const c = Object.assign({}, r);
  delete c.version;
  delete c.input;
  delete c.provenance;
  return c;
}

function compare(r, py, js) {
  const out = {name: r.name, set: r.set, samples: r.samples, cases: r.cases || undefined};
  if (!py.res) {
    out.native_error = "exit " + py.code + ": " + py.err.trim().split("\n").slice(-1)[0];
  }
  if (js.error) out.port_error = js.error;
  if (!py.res || !js.res) return out;
  const P = py.res, J = js.res;
  out.unsupported = {native: P.unsupported, port: J.unsupported, same: P.unsupported === J.unsupported};
  const conv = (P.provenance.files || []).find(f => f[0] === "converted");
  if (conv) out.conversion_same_text = js.convSha === conv[1];
  const e = hoeffding(r.samples);
  out.answers = [];
  const n = Math.max(P.answers.length, J.answers.length);
  for (let i = 0; i < n; i++) {
    const a = P.answers[i], b = J.answers[i];
    const row = {instance: a ? a.instance : null, instance_port: b ? b.instance : null};
    if (a && b) {
      row.native = a.counts;
      row.port = b.counts;
      row.identical = a.instance === b.instance && a.counts.join() === b.counts.join();
      if (!row.identical) {
        row.within_e = a.counts.every((c, k) => Math.abs(c - b.counts[k]) / r.samples <= e);
      }
    } else row.identical = false;
    out.answers.push(row);
  }
  out.whole_result_equal = firstDiff(comparable(P), comparable(J), "result") === null;
  if (!out.whole_result_equal) out.first_difference = firstDiff(comparable(P), comparable(J), "result");
  return out;
}

async function main() {
  const a = parseArgs(process.argv.slice(2));
  fs.mkdirSync(a.out, {recursive: true});
  for (const d of ["native", "port"]) fs.mkdirSync(path.join(a.out, d), {recursive: true});
  const runs = collectRuns(a);
  console.log(runs.length + " runs");
  const fname = r => r.name.replace(/[\/ ]/g, "_").replace(/[^A-Za-z0-9_.=()+-]/g, "") + ".json";

  // conversions for the port, one at a time
  for (const r of runs) {
    const ext = path.extname(r.file).toLowerCase();
    if (ext === ".js" || ext === ".json") {
      r.text = fs.readFileSync(r.file, "utf8");
      r.conv = null;
    } else {
      r.conv = convert(a, r.file);
      r.text = r.conv.stdout;
    }
  }

  // mcref.py, several processes at a time
  const py = new Array(runs.length);
  let done = 0;
  await pool(runs, a.jobs, async (r, i) => {
    py[i] = await runNative(a, r);
    done++;
    if (done % 10 === 0 || done === runs.length) console.log("mcref.py " + done + "/" + runs.length);
  });

  // the port, one run at a time in this process
  const js = [];
  for (const r of runs) {
    const o = {samples: r.samples, seed: 1, allAtoms: r.options.indexOf("--all-atoms") >= 0};
    const mg = r.options.indexOf("--max-ground");
    if (mg >= 0) o.maxGround = parseInt(r.options[mg + 1], 10);
    if (r.conv) {
      o.convertedBy = "gk -writejson -recursive";
      o.conversionOutput = r.conv.output;
    }
    const t0 = process.hrtime.bigint();
    let res = null, error = null;
    try { res = mcref(r.text, o); } catch (e) { error = String(e && e.stack || e); }
    const secs = Number(process.hrtime.bigint() - t0) / 1e9;
    js.push({res: res, error: error, secs: secs, convSha: r.conv ? sha256(r.conv.stdout) : null});
  }

  const results = runs.map((r, i) => {
    const c = compare(r, py[i], js[i]);
    c.secs = {native: +py[i].secs.toFixed(3), port: +js[i].secs.toFixed(3),
      conversion: r.conv ? +r.conv.secs.toFixed(3) : 0};
    if (py[i].res) fs.writeFileSync(path.join(a.out, "native", fname(r)), JSON.stringify(py[i].res, null, 1));
    if (js[i].res) fs.writeFileSync(path.join(a.out, "port", fname(r)), JSON.stringify(js[i].res, null, 1));
    return c;
  });
  fs.writeFileSync(path.join(a.out, "results.json"), JSON.stringify(results, null, 1));

  // the summary
  const lines = [];
  const w = s => { lines.push(s); console.log(s); };
  w("# mcref.js against mcref.py");
  w("");
  w("Seed 1. Times in seconds: mcref.py wall time per process (" + a.jobs + " processes at a time, gk's " +
    "conversion included), the port's time in node (conversion excluded), the conversion by gk alone.");
  w("");
  w("| set | runs | same unsupported | answers | identical counts | not identical, within e | " +
    "whole result equal | same gk conversion text | errors | mcref.py s | port s | conversion s |");
  w("|---|---|---|---|---|---|---|---|---|---|---|---|");
  const sets = ["semantics", "cases", "page"];
  for (const s of sets.concat(["all"])) {
    const rs = results.filter(x => s === "all" || x.set === s);
    if (!rs.length) continue;
    const ans = [].concat(...rs.map(x => x.answers || []));
    const sum = f => rs.reduce((t, x) => t + f(x), 0);
    w("| " + s + " | " + rs.length + " | " + rs.filter(x => x.unsupported && x.unsupported.same).length +
      " | " + ans.length + " | " + ans.filter(x => x.identical).length + " | " +
      ans.filter(x => !x.identical && x.within_e).length + " | " +
      rs.filter(x => x.whole_result_equal).length + " | " +
      rs.filter(x => x.conversion_same_text === true).length + " of " +
      rs.filter(x => x.conversion_same_text !== undefined).length + " | " +
      rs.filter(x => x.native_error || x.port_error).length + " | " +
      sum(x => x.secs.native).toFixed(1) + " | " + sum(x => x.secs.port).toFixed(1) + " | " +
      sum(x => x.secs.conversion).toFixed(1) + " |");
  }
  w("");
  w("## Per run");
  w("");
  w("| run | N | unsupported (native / port) | answer | native counts | port counts | identical | " +
    "whole equal | mcref.py s | port s |");
  w("|---|---|---|---|---|---|---|---|---|---|");
  for (const x of results) {
    const uns = x.unsupported ? (x.unsupported.same ? (x.unsupported.native === null ? "none" :
      x.unsupported.native) : x.unsupported.native + " / " + x.unsupported.port) :
      ("error: " + (x.native_error || "") + " " + (x.port_error || "").split("\n")[0]);
    const ansl = x.answers && x.answers.length ? x.answers : [null];
    ansl.forEach((an, k) => {
      w("| " + (k ? "" : x.name) + " | " + (k ? "" : x.samples) + " | " + (k ? "" : uns.replace(/\|/g, "\\|")) +
        " | " + (an ? an.instance : "") + " | " + (an && an.native ? an.native.join(" ") : "") + " | " +
        (an && an.port ? an.port.join(" ") : "") + " | " +
        (an ? (an.identical ? "yes" : (an.within_e ? "no, within e" : "no")) : "") + " | " +
        (k ? "" : (x.whole_result_equal ? "yes" : "no" + (x.first_difference ? " (" + x.first_difference + ")" : ""))) +
        " | " + (k ? "" : x.secs.native) + " | " + (k ? "" : x.secs.port) + " |");
    });
  }
  fs.writeFileSync(path.join(a.out, "summary.md"), lines.join("\n") + "\n");
}

main().catch(e => { console.error(e); process.exit(1); });
