# PLAN: Add a CDCL (conflict-driven clause learning) prover to logictools.org

> **Implementation record (2026-07-21): this plan has been carried out.**
> The delivered solver is `proplog_cdcl.js`; the site changes are in `prop.html`,
> `proplog.html`, `proplog_ui.js`, `download.html`, `about.html`,
> `closurecompiler.txt` and the rebuilt bundle `proplog_min.js`.
> Four things turned out differently from the plan below; the notes are kept
> because they explain why the shipped code looks the way it does.
>
> 1. **A soundness bug was found in `proplog_dpll.js` and fixed.** Its
>    `simplify_clause_list` did a single pass of unit propagation whose results
>    could contradict clauses it had already emitted, and nothing rechecked them.
>    On the clause set
>    `[[2,1,-4],[-4,-2,1],[-2,-1],[3,-2,-1],[4,1,3],[-4,3],[-2,1,-3],[-4,4,1],[-1,-2,4],[3,1,-1],[-1,2],[-2,1,-4],[-3],[-4,3,-1],[1,-2,3],[3,-2,2]]`
>    it answered SAT with the model `1 -2 -3 -4`, which falsifies `[-1,2]`; the
>    set is in fact unsatisfiable. The preprocessing has been removed from
>    `proplog_dpll.js` (with an explicit empty-clause check kept), as the site
>    author asked. `proplog_cdcl.js` keeps the same preprocessing but is safe,
>    because it propagates the units it finds through the watch lists before the
>    first decision - which is exactly what dpll never did.
> 2. **Clause database reduction and learned clause minimization were
>    implemented**, although §2.6 below said to leave them out. Without deletion
>    the learned clause set grew without bound and the solver lost to plain dpll
>    on everything above 200 variables, which would have made the whole page
>    misleading. See `reduce_learned` and `minimize_learned`.
> 3. **The constants were tuned on fixed benchmark sets** (see §5 of this record):
>    `RESTART_BASE=128`, `LEARNED_GROWTH=1.1`. Learned clauses are ranked by
>    length; LBD was implemented and measured as well, and was not consistently
>    better, so the simpler criterion was kept and LBD is mentioned in the code
>    comments as the modern alternative.
> 4. **The bundle is built with rjsmin, not terser** - no node is available in
>    this environment. rjsmin only strips comments and whitespace, so the bundle
>    is 70KB instead of the old Closure-compiled 29KB, but nothing is renamed and
>    hence nothing can break. `closurecompiler.txt` documents the command.
>
> **Verification.** 3616 automated checks pass, including 600 small random
> instances checked against brute force (for cdcl *and* for the fixed dpll), 400
> larger ones cross-checked against `naivedpll`, the truth table solver and dpll,
> all generated `all_combinations` and `small_unsat` problems, trace and
> statelessness tests. The same suite passes against the rebuilt `proplog_min.js`.
> In the browser, all eight selectbox options were exercised on both `prop.html`
> and `proplog.html`.
>
> **Honest performance summary.** On the site's own random 3-sat generator cdcl
> and the fixed dpll are roughly on par (cdcl was faster on 45 of 80 instances at
> 150-300 variables; the totals swing either way on a few heavy-tail instances).
> This is expected: uniform random problems have no structure for learned clauses
> to exploit. Calibration against the real kissat 1.0.3 binary on the hardest
> instance of the set: kissat needed 255698 conflicts and 6.8s, our solver 214168
> conflicts and 32s - i.e. comparable search quality, roughly 5x slower per
> conflict, which is what JavaScript costs. The site texts say this plainly
> instead of claiming cdcl is simply "the best".

Audience: the implementing model (Opus 4.8) working in this repository (`/opt/logictools`,
the source of https://logictools.org/). Read this file fully before starting.

Companion files in this directory (all referenced from the steps below):

- `ALGORITHM_cdcl.md` — the complete design of the new solver `proplog_cdcl.js`:
  data structures, function-by-function pseudocode, trace format, pitfalls.
- `texts_prop_html.md` — prepared, ready-to-paste replacement texts for `prop.html`.
- `texts_other_files.md` — prepared texts for `proplog.html`, `proplog_ui.js`,
  `download.html`, `about.html` and `closurecompiler.txt`.

## 1. Goal and context

logictools.org is an **educational** site. The propositional page `prop.html` lets a
visitor pick a solver from the "using" selectbox, run it on a formula or DIMACS input,
and optionally watch an html trace of the search. The point is that every solver is a
single, self-contained, heavily commented, easy-to-read javascript file that the
visitor is encouraged to open and study. The existing solvers form a pedagogical
ladder: `proplog_searchtable.js` (truth table) → `proplog_naivedpll.js` →
`proplog_olddpll.js` → `proplog_dpll.js` ("dpll: better", currently the best).

The task: add the next rung of the ladder — a
[Conflict-Driven Clause Learning](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)
solver — as a new file `proplog_cdcl.js`, selectable on `prop.html` as
**"cdcl: clause learning"** (option value `"cdcl"`), downloadable from
`download.html`, and described on `prop.html` help texts and `about.html`.
The new solver must read as an *extension and modification of `proplog_dpll.js`*:
same coding style, same module pattern, same helper functions, same call contract —
so a student can diff the two files mentally and see exactly what CDCL adds.
A high-level reference example of a real CDCL solver is
https://github.com/arminbiere/kissat (a checkout exists in `./kissat/` for browsing;
it is NOT part of the site and must not be committed or modified).

## 2. Hard constraints (do not deviate)

1. **File**: new solver in `proplog_cdcl.js` at the repo root, MIT licence header,
   copyright line `Copyright (c) 2026 Tanel Tammet (tanel.tammet at gmail.com)`.
2. **Module pattern**: identical to the other solvers:
   ```js
   (function(exports) {
     "use strict";
     ...
   })(this.proplog_cdcl = {});
   ```
   No ES6 modules, no `let`/`const`/arrow functions/classes — the whole file is
   ES5-style `var` code like `proplog_dpll.js`. No dependencies whatsoever.
3. **Call contract**, identical to `proplog_dpll.dpll`:
   ```js
   proplog_cdcl.cdcl(clauses, maxvarnr, trace, varnames)
   ```
   - `clauses`: array of integer arrays, e.g. `[[-1,2],[1],[-2]]`
   - `maxvarnr` (optional), `trace` (optional: false, "text", "html", "console" —
     and the UI in practice also passes the truthy string `"none"`, which must
     produce no per-step trace, exactly as in `proplog_dpll.js`),
   - `varnames` (optional array of original variable names).
   - Returns `[result, tracetext]` where `result` is `false` for unsatisfiable, or
     an array of assigned literals-as-shown-by-`showvar` for a model; `tracetext`
     is the human-readable trace/statistics string joined with `"\r\n"`.
4. **Educational commenting**: the file must be *more* commented than
   `proplog_dpll.js`. Every phase (preprocessing, propagation, decision, conflict
   analysis, backjumping, restarts) gets a block comment explaining the idea in
   plain language before the code; the conflict-analysis function includes a small
   worked example in its comment. A reader who knows `proplog_dpll.js` should be
   able to learn CDCL from this file alone.
5. **Selectbox naming**: option value `cdcl`, visible label `cdcl: clause learning`,
   placed FIRST in the selectbox (it becomes the default and best solver).
6. The full algorithm design is fixed in `ALGORITHM_cdcl.md`. Follow it; do not
   redesign (e.g. do not add clause-database reduction or clause minimization —
   they are deliberately left as commented "further extensions").

## 3. Steps

### Step 1 — implement `proplog_cdcl.js`

Follow `ALGORITHM_cdcl.md` in this directory. Summary of what the solver contains:

- reuse (copy, with comments) from `proplog_dpll.js`: the header/usage comment
  shape, `maxvar_and_meta`, `simplify_clause_list` preprocessing, the
  two-watched-literal bucket machinery (`posbuckets`/`negbuckets`, watch slots
  `clause[0]`/`clause[1]`), `store_model`, `print_trace`, `showvar`,
  `clause_to_str`;
- replace the recursive `satisfiable_at` search with the standard iterative CDCL
  loop over an explicit **trail**: propagate → decide → on conflict analyze
  (first-UIP), learn a clause, backjump non-chronologically;
- VSIDS-style variable activities with bump-and-decay (replacing the ad-hoc
  activity bumping of `proplog_dpll.js`), phase saving, and Luby-sequence
  restarts. Learned clauses are kept forever (no reduction — commented as an
  exercise).

Expected size: roughly 700–900 lines including comments.

### Step 2 — test the solver standalone with node

Write a throwaway test harness OUTSIDE the repo (use the session scratchpad
directory, do not commit test files). The modules attach to `this`, so load them
in node like this:

```js
// harness.js — run from /opt/logictools so the readFileSync paths resolve
var fs=require("fs");
(function(){
  eval(fs.readFileSync("proplog_dpll.js","utf8"));
  eval(fs.readFileSync("proplog_generate.js","utf8"));
  eval(fs.readFileSync("proplog_cdcl.js","utf8"));
}).call(global);
// now global.proplog_cdcl, global.proplog_dpll, global.proplog_generate exist
```

Required tests, all must pass:

1. **Tiny fixed cases** (clone the array before each call — solvers mutate input):
   - `[[1]]` → SAT with model containing `1`; `[[-1]]` → SAT with `-1`
   - `[[1],[-1]]` → UNSAT
   - `[[-1,2],[1],[-2]]` → UNSAT (the site's default example)
   - `[[-1,2],[1]]` → SAT; `[[1,2],[-1,2],[1,-2],[-1,-2]]` → UNSAT
   - `[[1,2],[-1,-2]]` → SAT
   - a case forcing a real backjump, e.g.
     `[[1,4],[1,-4,5],[-5,6],[-5,-6,7],[-7,-5,4],[2,3],[-2,3],[2,-3]]` — just
     assert SAT/UNSAT agreement with dpll and model validity.
2. **Model checker**: a function that takes the ORIGINAL clause list and the
   returned model (note: model entries are `showvar` output — with no `varnames`
   they are strings like `"3"`/`"-4"`; convert with `parseInt`) and verifies every
   clause contains a true literal. Every SAT answer in every test below must pass
   this check. Variables missing from the model default to unassigned — treat a
   clause as satisfied only via literals actually assigned true.
3. **Generated problems** (via `proplog_generate.generate_problem(n, type)`; it
   returns a DIMACS string — parse it with a few lines of `split`, or also load
   `proplog_parse.js` and use `proplog_parse.parse` then `shift()` the maxvar):
   - `all_combinations` for n = 2..12 → always UNSAT;
   - `small_unsat` for n = 2..12 → always UNSAT.
4. **Fuzz vs dpll**: ≥ 500 iterations of `random_3-sat` with n drawn from 4..30:
   `proplog_cdcl.cdcl` and `proplog_dpll.dpll` must agree SAT/UNSAT on every
   instance (deep-clone the clause array before each solver call!), and each
   cdcl model must pass the model checker.
5. **Performance sanity**: `random_3-sat` with 200 variables must complete well
   under 10 seconds (typically < 1s); `all_combinations` with 12 variables
   (4096 clauses) must complete in a few seconds at most. On unsatisfiable
   generated instances the cdcl conflict count should generally be far below the
   dpll unit-propagation count — print both to eyeball that learning is working.
6. **Trace smoke test**: run the default example with trace `"text"`, `"html"`,
   `"console"`, `"none"` and `varnames` (e.g. `[0,"a","b"]`) — no crashes, the
   `"text"` trace shows decisions, propagations with reason clauses, conflicts,
   learned clauses and backjump levels, and the final statistics line.
7. **Statelessness**: calling `cdcl` twice in a row on different inputs gives
   correct answers both times (all state must be reset at entry — beware module
   globals like `result_model` and `trace_list`; `proplog_dpll.js` resets them at
   the top of the exported function, do the same).

### Step 3 — integrate into the site

Apply the prepared texts, in this order:

1. `proplog_ui.js` — dispatch + header comment: see `texts_other_files.md` §1.
2. `prop.html` — selectbox option, help texts, modal texts, keywords, commented
   script list: see `texts_prop_html.md` (7 edits, exact before/after blocks).
3. `proplog.html` (the barebones no-design page) — option + script tag:
   see `texts_other_files.md` §2.
4. `download.html` — new file entry, description shuffle, release date:
   see `texts_other_files.md` §3.
5. `about.html` — best-solver sentence, methods section, state-of-the-art
   section, keywords: see `texts_other_files.md` §4.
6. `closurecompiler.txt` — add the new file and document the current build
   command: see `texts_other_files.md` §5.

The prepared texts are authoritative for wording; if surrounding code has drifted
from the quoted "old" blocks, adapt minimally but keep the new wording.

### Step 4 — rebuild `proplog_min.js`

`prop.html` does NOT load the individual solver files — it loads only the
minified bundle `proplog_min.js` (see the bottom of `prop.html`; the individual
`<script>` tags there are commented out). The bundle was historically built with
the now-retired Google Closure Compiler online service (`closurecompiler.txt`).
Rebuild it locally with terser instead — safe here because every module is an
IIFE communicating only through `this.proplog_*` globals:

```bash
cd /opt/logictools
npx terser proplog_ui.js proplog_parse.js proplog_convert.js \
    proplog_generate.js proplog_dpll.js proplog_olddpll.js \
    proplog_naivedpll.js proplog_searchtable.js proplog_naiveres.js \
    proplog_res.js proplog_cdcl.js \
    --compress --mangle -o proplog_min.js
```

Do NOT pass `--toplevel` or `--mangle-props` (they would break the cross-file
globals). If `npx terser` is unavailable and cannot be installed, fallback: edit
`prop.html` to load the individual files by replacing the
`<script src="proplog_min.js"></script>` line with the commented-out script list
(plus `proplog_cdcl.js`) — functionally identical, slightly slower to load.

### Step 5 — verify in the browser

Serve the site locally (`python3 -m http.server 8080` in `/opt/logictools`) and
open `http://localhost:8080/prop.html`. Verify, ideally with the browser
automation tools, otherwise ask the user to check:

1. "cdcl: clause learning" appears first in the "using" selectbox and is the
   default.
2. Solve the default formula `(a -> b) & a & -b` with cdcl → reports
   "Clause set is **false** for all possible assignments to variables."
3. Solve `(a -> b) & a` with cdcl → reports true with an assignment using the
   original names `a`, `b`.
4. Generate a `random 3-sat` problem for 200 variables, solve with cdcl (no
   trace) → answer within seconds; re-solve with "dpll: better" → same
   SAT/UNSAT verdict.
5. Generate `all combinations` for 10 variables → cdcl reports false.
6. Run the small default example with "html trace" → the trace renders as
   indented html lines showing decisions/conflicts/learned clauses.
7. Every OTHER selectbox option still works (the bundle rebuild touches them
   all): dpll better/old/naive, both truth tables, both resolutions.
8. Repeat check 2 on `proplog.html` (which loads individual files, catching any
   bundle-only mistake) and confirm `download.html` and `about.html` render with
   the new texts and working `proplog_cdcl.js` links.

### Step 6 — finish

1. Re-read `proplog_cdcl.js` top to bottom once, as a student would: fix any
   comment that lags the code.
2. `git status` — the commit should contain exactly: `proplog_cdcl.js` (new),
   `proplog_min.js` (rebuilt), `proplog_ui.js`, `prop.html`, `proplog.html`,
   `download.html`, `about.html`, `closurecompiler.txt`, and this `cdcl_plan/`
   directory. Do not commit test harnesses, `node_modules`, or anything from the
   untracked reference checkouts (`kissat/`, `cadical/`, `minisat-wasm/`, etc.).
3. Commit on master with a message in the style of the repo's history, e.g.
   `Propositional page: the cdcl clause-learning prover, texts and downloads`.
   Do not push unless the user asks.

## 4. Acceptance criteria

- All Step 2 tests pass; fuzz agreement with dpll on ≥ 500 random instances.
- All Step 5 browser checks pass.
- `proplog_cdcl.js` follows every constraint in §2 and the design in
  `ALGORITHM_cdcl.md`, and is understandable standalone.
- Site texts match the prepared texts; the release date on `download.html` is
  the actual date of the work.

## 5. Known pitfalls (read before coding)

These are repo-specific traps discovered while preparing this plan; the
algorithm-level pitfalls are in `ALGORITHM_cdcl.md` §8.

1. **`"none"` trace value is truthy.** `prop.html` passes the string `"none"`
   through `proplog_ui.solve` straight into the solver. `proplog_dpll.js` then
   sets `trace_flag=true` with `trace_method="none"`, and `print_trace` silently
   ignores the unknown method. Copy this exact behavior; do not "fix" it
   differently from the other solvers.
2. **Solvers mutate their input.** `maxvar_and_meta` rebuilds clauses as
   `Int32Array`s with 2 leading meta slots and `simplify_clause_list` drops/edits
   clauses. Fine in the UI (each Solve re-parses), but your tests must clone
   inputs before comparing solvers, and the model checker must check against the
   original clause list.
3. **The dispatch chain in `proplog_ui.js` mixes `if` and `else if`** (a latent
   bug: two `if`s restart the chain). The prepared text in
   `texts_other_files.md` §1 replaces the whole chain with a clean `else if`
   ladder including `cdcl` — use it as given.
4. **Bucket capacity**: `proplog_dpll.js`'s bucket arrays are sized by the
   initial clause set; learned clauses added later can overflow a bucket's
   placeholder slots. Always append watches through the bounds-checked
   `addwatch` helper specified in `ALGORITHM_cdcl.md` §4 — including inside the
   watch-move code adapted from `unit_propagate`.
5. **Model entries are `showvar` strings**, not integers, when the result is
   printed (`store_model` pushes `showvar(...)`). Keep this: the UI joins them
   with spaces and the trace shows original variable names when available.
6. **`propositional.html` and `index.html` need no changes** (checked: no solver
   lists there). `README.md` lists no individual files either — no change needed.
