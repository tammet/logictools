// Verification harness for the commonsense reasoner page.
//
// It reads the example inputs directly out of commonsense.html and runs each
// one through the checked-in WebAssembly build gkjs.js with the exact argument
// list the page builds for that example (from its Advanced-panel presets),
// then checks that the expected key lines appear in the output.
//
// Each example runs in a FRESH child process: the page runs each solve in a
// fresh Web Worker for the same reason (gk keeps options in static globals
// that are not reset between callMain calls). One child = one module = no
// cross-example leakage.
//
// Run with the Emscripten node that matches the build:
//   /opt/gkcjs/emsdk/node/12.18.1_64bit/bin/node commonsense_check.js
//
// Exit status is non-zero if any example fails.

var fs = require("fs");
var path = require("path");
var child_process = require("child_process");

var DIR = __dirname;
var PAGE = path.join(DIR, "commonsense.html");
var GKJS = path.join(DIR, "gkjs.js");
var KB = path.join(DIR, "gk_axioms_std.js");

// Per-example argument lists (flags after the input file names) exactly as the
// page's buildArgs() produces them from each example's preset, and the key
// lines that must appear in the output.
var STRAT_ARITH = '{"strategy":["unit"],"query_preference":0,"arith_instantiation":1}';
var STRAT_NL = '{"strategy": ["negative_pref", "posunitpara"], "query_preference": 1}';

var EXAMPLES = {
  "1":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: polly", "confidence: 1"] },
  "2":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: true", "confidence: 0.56"] },
  "3":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: true", "confidence: 0.8", "cumul"] },
  "4":  { flags: ["-seconds","5","-detail","-print","10"], kb: false,
          expect: ["confidence: 0.3", "support: 0.3 for, 0 against", "conflict: 0.4", "ignorance: 0.3", "CONTESTED"] },
  "5":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: true", "confidence: 0.3764"] },
  "6":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: true", "confidence: 0.846"] },
  "7":  { flags: ["-seconds","5","-detail","-print","10"], kb: false,
          expect: ["confidence: 0.27", "conflict: 0", "ignorance: 0.73", "CONTESTED"] },
  "8":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: b", "answer: a", "blockers: unless(-flies(b), 2)", "confidence: 1"] },
  "9":  { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: b", "answer: a", "confidence: 0.1"] },
  "10": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: b", "rejected answer: p", "confidence against: 1"] },
  "11": { flags: ["-seconds","5","-detail","-print","10"], kb: false,
          expect: ["evidence below limit", "rejected answer: n", "confidence against: 0", "CONTESTED"] },
  "12": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ['[["$ans","sit2"]]', "rejected_answers"] },
  "13": { flags: ["-seconds","5","-print","10","-strategytext",STRAT_ARITH], kb: false,
          expect: ["answer: 8", "confidence: 0.8"] },
  "14": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ['"answer": true', '"confidence": 1.0000'] },
  "15": { flags: ["-seconds","5","-detail","-print","10"], kb: false,
          expect: ['"confidence": 0.2520', '"bird","a"', '0.7000', "CONTESTED"] },
  "16": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ['"answer": true', '"confidence": 0.5600'] },
  "17": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["answer: true", "confidence: 0.56"] },
  "18": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ["SZS status GaveUp", "rejected answer: p", "confidence against: 0.08"] },
  "19": { flags: ["-seconds","5","-print","10"], kb: false,
          expect: ['"answer": true', '"confidence": 1.0000', '["flies","b1"]'] },
  "20": { flags: ["-seconds","30","-print","10","-maxanswers","1"], kb: false,
          expect: ["answer: do(putdown(c,b),do(pickup(c),do(putdown(b,a),do(pickup(b),s0))))", "confidence: 1"] },
  "21": { flags: ["-seconds","5","-print","10","-confidence","0.1","-strategytext",STRAT_NL], kb: true,
          expect: ['"answer": false'] },
  "22": { flags: ["-seconds","5","-print","10","-confidence","0.1","-strategytext",STRAT_NL], kb: true,
          expect: ['["$ans","$some_fox"]'] }
};

// Extract one example's input text from commonsense.html, undoing the same
// three HTML escapes selectExample() undoes in the browser.
function readInput(id) {
  var page = fs.readFileSync(PAGE, "utf8");
  var re = new RegExp('<code id="example_cs' + id + '_input_code">([\\s\\S]*?)</code>');
  var m = page.match(re);
  if (!m) throw new Error("no input_code for example " + id);
  return m[1]
    .replace(/&amp;/g, "&")
    .replace(/&gt;/g, ">")
    .replace(/&lt;/g, "<");
}

// ---- child mode: run one example through the wasm and print its output -----

if (process.argv[2] === "--run") {
  var id = process.argv[3];
  var ex = EXAMPLES[id];
  var input = readInput(id);
  var files = ex.kb ? ["axioms_std.js", "input"] : ["input"];
  var args = files.concat(ex.flags);
  var kbText = ex.kb ? fs.readFileSync(KB, "utf8") : null;
  process.argv = [process.argv[0], GKJS, "-version"];
  var M = require(GKJS);
  M.onRuntimeInitialized = function () {
    if (kbText !== null) M.FS.writeFile("axioms_std.js", kbText);
    M.FS.writeFile("input", input);
  };
  M.postRun = [function () {
    process.stdout.write("===GKSTART===\n");
    try { M.callMain(args); } catch (e) { process.stdout.write("[exception] " + e + "\n"); }
  }];
  return;
}

// ---- parent mode: run all examples, check expectations ---------------------

var ids = Object.keys(EXAMPLES);
var pass = 0, fail = 0;
var failures = [];

for (var i = 0; i < ids.length; i++) {
  var id = ids[i];
  var res = child_process.spawnSync(process.execPath, [__filename, "--run", id],
    { encoding: "utf8", maxBuffer: 64 * 1024 * 1024, timeout: 90000 });
  var out = res.stdout || "";
  var idx = out.indexOf("===GKSTART===");
  var body = idx >= 0 ? out.slice(idx + "===GKSTART===".length) : out;
  var missing = EXAMPLES[id].expect.filter(function (s) { return body.indexOf(s) < 0; });
  if (missing.length === 0) {
    pass++;
    console.log("PASS  ex" + id);
  } else {
    fail++;
    failures.push(id);
    console.log("FAIL  ex" + id + "  missing: " + JSON.stringify(missing));
    var preview = body.split("\n").filter(function (l) { return l.trim(); }).slice(0, 6).join("\n    ");
    console.log("    output head:\n    " + preview);
  }
}

console.log("\n" + pass + " passed, " + fail + " failed" +
  (failures.length ? " (" + failures.map(function (x) { return "ex" + x; }).join(", ") + ")" : ""));
process.exit(fail ? 1 : 0);
