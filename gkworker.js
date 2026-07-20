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

var Module = {
  noInitialRun: true,
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
    Module.FS.writeFile("input", j.input);
    gkout = "";
    try { Module.callMain(j.args); } catch (e) { /* emscripten exit() throws ExitStatus; normal */ }
  } catch (e) {
    gkout += "\n[worker error] " + e;
  }
  self.postMessage({ output: gkout });
}

importScripts("gkjs.js");
