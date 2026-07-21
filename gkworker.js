// Web Worker that runs one gk (gkjs.wasm) search and returns its output.
//
// A fresh worker is spawned for every solve (see useGk in commonsense.html).
// This matters: gk keeps its command-line options in static globals that are
// not reset between callMain() calls, so reusing one module instance would let
// one example's -maxanswers / -detail / -strategytext leak into the next. A
// new worker means a new module with all globals zero-initialised. Running in
// a worker also keeps the page responsive while a long search (e.g. planning)
// is in progress.

var gkout = "";
var job = null;
var ready = false;

// The solver files are cached by the browser like any other file, and a
// cached older pair would answer with an older gk. Both are therefore
// fetched under the build version: the loader below carries it in its own
// URL, locateFile puts it on the .wasm request the loader makes. Raise it
// whenever gkjs.js/gkjs.wasm are replaced.
var GK_BUILD = "1.0.6";

var Module = {
  noInitialRun: true,
  locateFile: function (p) { return p + "?v=" + GK_BUILD; },
  print: function (s) { gkout += s + "\n"; },
  printErr: function (s) { /* wasm diagnostics are not part of the answer */ },
  onRuntimeInitialized: function () { ready = true; maybeRun(); }
};

self.onmessage = function (ev) { job = ev.data; maybeRun(); };

function maybeRun() {
  if (!job || !ready) return;
  var j = job; job = null;
  try {
    if (j.kb !== null && j.kb !== undefined) Module.FS.writeFile("axioms_std.js", j.kb);
    if (j.datafiles) {
      // extra data files (e.g. the -defaults taxonomy tables), already
      // decompressed by the page; data is a Uint8Array
      for (var i = 0; i < j.datafiles.length; i++)
        Module.FS.writeFile(j.datafiles[i].name, j.datafiles[i].data);
    }
    Module.FS.writeFile("input", j.input);
    gkout = "";
    try { Module.callMain(j.args); } catch (e) { /* emscripten exit() throws ExitStatus; normal */ }
  } catch (e) {
    gkout += "\n[worker error] " + e;
  }
  self.postMessage({ output: gkout });
}

importScripts("gkjs.js?v=" + GK_BUILD);
