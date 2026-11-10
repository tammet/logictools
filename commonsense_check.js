// Verification harness for the commonsense reasoner page (gk 1.2.5).
//
// For each example of commonsense.html it reads the input and the Advanced
// preset out of the page, builds the argument list with the page's own
// buildArgs(), runs the checked-in WebAssembly build gkjs.js with the files
// the page passes (the background axioms and the taxonomy tables where the
// example needs them), and checks the {"recursive": ...} line: every answer
// with its four shares (within 0.0005 of the values below, recorded with
// gk 1.2.5 on 2026-11-10), and the proofs of each answer with support for or
// against. Answers are named by their text form (gkproofs.js litText).
//
// Each example runs in a FRESH child process: the page runs each solve in a
// fresh Web Worker for the same reason (gk keeps options in static globals
// that are not reset between callMain calls).
//
// Run with node 16 or later:   node commonsense_check.js [example ids...]
// Exit status is non-zero if any example fails.

var fs = require("fs");
var path = require("path");
var vm = require("vm");
var child_process = require("child_process");

var DIR = __dirname;
var PAGE = path.join(DIR, "commonsense.html");
var GKJS = path.join(DIR, "gkjs.js");
var KB = path.join(DIR, "gk_axioms_std.js");
var GkProofs = require(path.join(DIR, "gkproofs.js"));

// the answers and their four shares (for, against, conflict, ignorance)
var EXPECT = {
  "1": [["flies(tweety)", [1, 0, 0, 0]], ["flies(pingu)", [0, 1, 0, 0]]],
  "2": [["rain(today)", [0.56, 0, 0, 0.44]]],
  "3": [["rain(today)", [0.8, 0, 0, 0.2]]],
  "4": [["flies(tweety)", [0.3, 0, 0.4, 0.3]]],
  "5": [["smokes(sam)", [0.3804, 0, 0, 0.6196]]],
  "6": [["rain_likely(today)", [0.846, 0, 0, 0.154]]],
  "7": [["flies(tweety)", [0.27, 0, 0, 0.73]]],
  "8": [["flies(tweety)", [1, 0, 0, 0]], ["flies(robin)", [1, 0, 0, 0]]],
  "9": [["flies(tweety)", [0.1, 0.9, 0, 0]], ["flies(robin)", [1, 0, 0, 0]]],
  "10": [["flies(tweety)", [1, 0, 0, 0]], ["flies(pingu)", [0, 1, 0, 0]]],
  "11": [["dislikeswar(nixon)", [0, 0, 0, 1]]],
  "12": [["at(john,kitchen,s3)", [1, 0, 0, 0]], ["at(john,hallway,s3)", [0, 0, 0, 1]]],
  "13": [["boxes_needed(7)", [0.8, 0, 0, 0.2]]],
  "14": [["lives_in(alice,tallinn)", [1, 0, 0, 0]]],
  "15": [["flies(tweety)", [0.252, 0, 0, 0.748]]],
  "16": [["rain(today)", [0.56, 0, 0, 0.44]]],
  "17": [["rain(today)", [0.56, 0, 0, 0.44]]],
  "18": [["-flies(p)", [0.72, 0, 0, 0.28]]],
  "19": [["flies(b1)", [1, 0, 0, 0]]],
  "20": [["goal(do(putdown(c,b),do(pickup(c),do(putdown(b,a),do(pickup(b),s0)))))", [1, 0, 0, 0]]],
  "21": [["$defq0", [0, 1, 0, 0]]],
  "22": [["$defq0($some_fox)", [1, 0, 0, 0]]],
  "23": [["isa(b1,organism)", [0.5731, 0.0179, 0.3821, 0.0269]], ["isa(a1,organism)", [0, 0.4, 0.6, 0]]],
  "24": [["flies(tweety)", [0.396, 0.56, 0, 0.044]]],
  "25": [["flies(tweety)", [0.396, 0.56, 0, 0.044]]],
  "26": [["flies(tweety)", [0.6984, 0.224, 0, 0.0776]]],
  "27": [["flies(tweety)", [0.6984, 0.224, 0, 0.0776]]]
};

var TOL = 0.0005;

// Extract one example's input text from commonsense.html, undoing the same
// three HTML escapes selectExample() undoes in the browser.
function readInput(page, id) {
  var re = new RegExp('<code id="example_cs' + id + '_input_code">([\\s\\S]*?)</code>');
  var m = page.match(re);
  if (!m) throw new Error("no input_code for example " + id);
  return m[1].replace(/&amp;/g, "&").replace(/&gt;/g, ">").replace(/&lt;/g, "<");
}

// The page's main script in a context with a stand-in document: the
// presets and the argument list of every example, as useGk() builds them.
function pageArgs(page, id) {
  var scripts = [];
  page.replace(/<script>([\s\S]*?)<\/script>/g, function (_, s) { scripts.push(s); return ""; });
  var main = scripts.filter(function (s) { return s.indexOf("function buildArgs") >= 0; })[0];
  var els = {};
  function el(x) {
    if (!els[x]) els[x] = { id: x, value: "", checked: false, disabled: false, style: {}, innerHTML: "" };
    return els[x];
  }
  var ctx = { document: { getElementById: el }, JSON: JSON, Math: Math, String: String, Array: Array,
              Object: Object, isNaN: isNaN, parseInt: parseInt, parseFloat: parseFloat, navigator: {} };
  vm.createContext(ctx);
  vm.runInContext(main, ctx);
  vm.runInContext("resetAdvanced()", ctx);
  var p = vm.runInContext("examplePresets[" + JSON.stringify(id) + "] || {}", ctx);
  ctx.__p = p;
  vm.runInContext("applyPreset(__p)", ctx);
  var flags = vm.runInContext("buildArgs()", ctx);
  var files = p.background ? ["axioms_std.js", "input"] : ["input"];
  if (p.taxonomy) files.push("-defaults");
  return { args: files.concat(flags), kb: !!p.background, tax: !!p.taxonomy };
}

// ---- child mode: run one example through the wasm and print its output -----

if (process.argv[2] === "--run") {
  var page0 = fs.readFileSync(PAGE, "utf8");
  var id0 = process.argv[3];
  var run = pageArgs(page0, id0);
  var input = readInput(page0, id0);
  var kbText = run.kb ? fs.readFileSync(KB, "utf8") : null;
  var taxFiles = null;
  if (run.tax) {
    var zlib = require("zlib");
    taxFiles = [
      ["gk_name_number.txt", zlib.gunzipSync(fs.readFileSync(path.join(DIR, "gk_name_number.txt.gz")))],
      ["gk_taxonomy_packed.txt", zlib.gunzipSync(fs.readFileSync(path.join(DIR, "gk_taxonomy_packed.txt.gz")))]
    ];
  }
  process.argv = [process.argv[0], GKJS, "-version"];
  var M = require(GKJS);
  M.onRuntimeInitialized = function () {
    if (kbText !== null) M.FS.writeFile("axioms_std.js", kbText);
    if (taxFiles) for (var t = 0; t < taxFiles.length; t++) M.FS.writeFile(taxFiles[t][0], taxFiles[t][1]);
    M.FS.writeFile("input", input);
  };
  M.postRun = [function () {
    process.stdout.write("===GKSTART===\n");
    try { M.callMain(run.args.slice()); } catch (e) { process.stdout.write("[exception] " + e + "\n"); }
  }];
  return;
}

// ---- parent mode: run the examples, check the line ---------------------------

function recursiveLine(text) {
  var lines = text.split("\n");
  for (var i = 0; i < lines.length; i++)
    if (lines[i].indexOf('{"recursive"') === 0) {
      try { return JSON.parse(lines[i]).recursive; } catch (e) { return null; }
    }
  return null;
}

function check(id, body) {
  var r = recursiveLine(body);
  if (!r) return ["no {\"recursive\": ...} line"];
  var got = Array.isArray(r.answers) ? r.answers
          : [{ answer: r.question, value: r.value, proof: r.proof }];
  var problems = [];
  EXPECT[id].forEach(function (e) {
    var a = null;
    for (var i = 0; i < got.length; i++) if (GkProofs.litText(got[i].answer) === e[0]) a = got[i];
    if (!a) { problems.push("no answer " + e[0]); return; }
    var v = a.value || [];
    for (var k = 0; k < 4; k++)
      if (!(Math.abs((v[k] || 0) - e[1][k]) <= TOL)) {
        problems.push(e[0] + ": (" + v.join(", ") + ") instead of (" + e[1].join(", ") + ")");
        break;
      }
    if ((e[1][0] > 0 || e[1][1] > 0) &&
        !(a.proof && ((a.proof["for"] || []).length || (a.proof.against || []).length)))
      problems.push(e[0] + ": no proof");
  });
  if (got.length !== EXPECT[id].length)
    problems.push(got.length + " answers instead of " + EXPECT[id].length);
  return problems;
}

var ids = process.argv.length > 2 ? process.argv.slice(2) : Object.keys(EXPECT);
var pass = 0, fail = 0, failures = [];
for (var i = 0; i < ids.length; i++) {
  var id = ids[i];
  var t0 = Date.now();
  var res = child_process.spawnSync(process.execPath, [__filename, "--run", id],
    { encoding: "utf8", maxBuffer: 256 * 1024 * 1024, timeout: 180000 });
  var out = res.stdout || "";
  var idx = out.indexOf("===GKSTART===");
  var body = idx >= 0 ? out.slice(idx + "===GKSTART===".length) : out;
  var problems = EXPECT[id] ? check(id, body) : ["no expectation for example " + id];
  var secs = ((Date.now() - t0) / 1000).toFixed(1) + " s";
  if (!problems.length) {
    pass++;
    console.log("PASS  ex" + id + "  (" + secs + ")");
  } else {
    fail++;
    failures.push(id);
    console.log("FAIL  ex" + id + "  (" + secs + "): " + problems.join("; "));
  }
}
console.log("\n" + pass + " passed, " + fail + " failed" +
  (failures.length ? " (" + failures.map(function (x) { return "ex" + x; }).join(", ") + ")" : ""));
process.exit(fail ? 1 : 0);
