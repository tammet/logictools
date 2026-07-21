# Plan: sampling check (Monte Carlo) on commonsense.html

Implementation plan for Opus 4.8. Adds the two viable stages from
`ANALYSIS_montecarlo_web.md` to the page:

1. **threshold sampling** — the four-mass estimate, no proof search per trial;
2. **inclusion sampling** — provability / net-confidence estimates, one wasm
   proof search per sampled world, module reuse inside Web Workers.

Reference implementations (the semantics to port, not to redesign):
`/opt/gkreasoner/montecarlo/gkmc.py`, `/opt/gkreasoner/montecarlo/threshold_worlds.py`,
documented in `/opt/gkreasoner/montecarlo/README.md`. Read all three before
writing code. The page to modify is `/opt/logictools/commonsense.html`; the
deployed wasm `gkjs.js`/`gkjs.wasm` (gk 1.0.2) is used unchanged — **no gk or
gkc source changes, no version bump, no rebuild**.

## 1. Measured facts the design relies on

These were measured with the deployed gkjs.wasm under node 12 (see
ANALYSIS_montecarlo_web.md); do not re-derive them, but keep them true:

- One wasm module instance can run `callMain` thousands of times: 2000
  consecutive world decisions, no failures, no slowdown, flat memory.
  Per decision: 18 ms (trivial world) – 55 ms (world with blockers).
  Four concurrent instances give ~3.4× throughput.
- gk keeps CLI options in static globals that are **not all reset** between
  `callMain` calls. Verified consequences:
  - a `-defworlds -clausify -outformat json` call does NOT corrupt later
    `-nonegative -plain` world runs in the same instance;
  - world runs DO corrupt a later plain run (`-plain`, `-nonegative`,
    `-outformat` leak). Therefore in any instance the order must be:
    reference run first, clausify second, world runs last — and world runs
    all use identical flags.
- `input -defworlds -clausify -outformat json` returns the versioned
  `gk_clauses_v1` export (JSON-array clauses, per-clause `@confidence`,
  `@head`, goals marked `@role:"goal"`) for ANY input syntax the page
  accepts, GKP included. This replaces all input parsing in JS.
- `input -detail -outformat json` returns machine-parseable JSON with
  `confidence` and `detail.support_for / support_against / conflict /
  ignorance` per answer, for any input syntax.
- `gk FILE -writejson` (native, CLI) converts GKP to the JSON-LD-LOGIC form
  that `gkmc.py` requires — used only in the verification harness.

## 2. Deliverables

| file | content |
|---|---|
| `/opt/logictools/mcsampler.js` | new Web Worker: setup (reference run + clausify + grounding + eligibility), inclusion trial loop, threshold evaluation, aggregation |
| `/opt/logictools/commonsense.html` | sampling row in the Advanced panel, page-side coordinator JS, one new modal, one modelinks entry |
| `/opt/logictools/mc_check.js` | node verification harness (pattern of `commonsense_check.js`) |

Not touched: `gkworker.js`, `gkjs.js`/`gkjs.wasm`, the navbar (the tab stays
hidden), the example texts, the other pages. Never delete any file.

## 3. Architecture

### 3.1 Worker pool

- The page spawns `W = Math.min(4, Math.max(1, (navigator.hardwareConcurrency || 2) - 1))`
  instances of `mcsampler.js` per sampling run. Worker 0 is the setup worker;
  all W workers (including 0) then run trial ranges. A new Sample click or
  Stop terminates all of them (same pattern as the existing fresh-worker
  solve). Never more than 4 wasm instances.
- `mcsampler.js` calls `importScripts("gkjs.js")` lazily, on the first
  message that needs the module, with the same `Module` shape as
  `gkworker.js` (`noInitialRun: true`, `print` collecting output,
  `printErr` ignored). Threshold evaluation needs no module, but its setup
  does, so in practice every worker 0 loads it.
- Per-instance call order (from the leak constraint): worker 0 runs
  (A) reference, (B) clausify, then world runs; workers 1..W-1 run world
  runs only. All world runs use exactly
  `["input", "-nonegative", "-plain", "-seconds", "2"]`.

### 3.2 Message protocol (page ⇄ worker)

Page → worker:

- `{cmd:"setup", input, seconds}` — worker 0 only. Runs
  (A) `["input", "-detail", "-outformat", "json", "-seconds", ""+seconds]`
  → parse gk's own answers (`confidence` and the four `detail` masses);
  (B) `["input", "-defworlds", "-clausify", "-outformat", "json"]`
  → the `gk_clauses_v1` items. Then grounds the pool and checks
  eligibility (section 5). Replies `{ok:true, gkExact, pool, questions,
  warnings}` or `{ok:false, refusal:"..."}`. `pool` is
  `[[origIdx, clause], ...]` plus a parallel `confs` array — plain JSON,
  small for every eligible input.
- `{cmd:"trials", pool, confs, questions, draws, seed, from, to}` — decide
  worlds `from..to-1`. Progress message every 25 trials:
  `{progress:{done, from, to}}`. Final: `{done:true, results:[{trial,
  keys:[...]} ...], timeouts}` where `keys` are the proved answer keys of
  that world.
- `{cmd:"pair", pool, confs, questions, draws, seed, answerKey, posQ, negQ,
  trials:[...]}` — the per-answer pairing pass (section 4.4): re-generate
  each listed world deterministically, decide the closed positive and
  negated instances, reply per-trial cells.
- `{cmd:"threshold", pool, confs, query, trials, seed}` — pure JS threshold
  evaluation (section 4.6), replies the four masses or a not-scored reason.

Page side merges results, computes the statistics (section 4.5), renders
progress and the final table. All page-side coordinator code lives inline in
commonsense.html next to the existing solver JS, same style (plain JS,
`gid()`, no new libraries).

### 3.3 Determinism

Seed is fixed at 0 (no UI control). World `t` must be reproducible from
`(seed, t)` alone, independent of worker split and of the phase that
re-creates it: port `gkmc.Runner.sample` — a per-trial RNG seeded by the
string `seed + ":" + t`. JS has no seedable RNG, so use mulberry32 (or
xoshiro) seeded from a 32-bit FNV-1a hash of that string. Results will match
the Python reference statistically (overlapping confidence intervals), not
bitwise; the harness checks intervals, not digits.

## 4. Porting specification

Port semantics 1:1 from the Python files; where the JS pipeline differs
(clausified export instead of original-statement parsing), that difference
is stated here and covered by verification. Keep the ports in `mcsampler.js`
with comments naming the Python function each block ports.

### 4.1 Pool construction (port of `ground_pool`, gkmc.py)

Input: the `gk_clauses_v1` items from run B (drop the leading meta object;
assert `format=="gk_clauses_v1"` and refuse otherwise, like
`load_clausified`). Differences from the Python flow, which pairs plain
`-clausify` output with the parsed original file:

- confidences come from the export's per-clause `@confidence` (the
  root-split values), not from original statements;
- question detection: items with `@role:"goal"`; drop
  `@name:"$auto_negated_question"` items entirely;
- statement grouping for `--draws shared` and for the multi-clause warning:
  consecutive runs of the same `@name`, as in Python.

Then as in Python: collect constants from all clauses (walk atoms, skipping
`$`-prefixed heads' structural parts, `?:` variables); ground every
non-goal clause over all constant tuples for its variables; dedupe per
statement; cap the pool at 100,000 ground clauses and refuse beyond it.
Keep Python's warning for uncertain multi-clause statements verbatim
(adapted wording, section 6.4).

The page always uses per-instance draws (`draws:"per-instance"`), matching
the gkmc default; the code should still implement `shared` (one draw per
statement) since it is a few lines and the harness can exercise it.

### 4.2 Question reconstruction

The Python tool writes the original `@question` into each world; the export
has only the negated goal clause. Reconstruct: from a goal clause, remove
any `$ans` literal; exactly one literal must remain; the question is that
literal with its sign flipped (`["-flies","?:0"]` → `flies(?:0)`, with
`?:N` variables kept as-is — gk accepts them in JSON questions). Refuse
goals that leave more than one literal ("sampling supports single-literal
questions only"). Multiple separate goal statements → refuse for the
subtract pairing pass exactly as Python does (fall back to provability with
the same warning).

### 4.3 World runs and answer parsing

World document: JSON array of `{"@name":"w<i>","@logic":<ground clause>}`
for each retained clause, plus `{"@question": <reconstructed question>}`.
`FS.writeFile("input", JSON.stringify(doc))`, then `callMain` with the
fixed world flags. Timeout: a world exceeding `-seconds 2` returns a
time-limit result; count it as a timeout (invalid trial), as Python does.

Parsing (port of `parse_world_answers` + `norm_key`, but on JSON): the
world input is JSON, so the output is JSON — `JSON.parse` the collected
output; on parse failure treat the trial as an error/timeout. From
`answers[]`: `answer === true` → key `"yes"`; `answer === false` → no key;
an `$ans` form (`[["$ans", v1, ...]]`) → key = the values joined with
`","`. `"no information"` / `"no answers found"` / time-limit results → no
keys.

### 4.4 Semantics: provable and subtract (port of gkmc.py main flow)

- **provable**: fraction of valid worlds whose keys contain the answer,
  Wilson interval.
- **subtract** (default): phase 1 as above discovers answers; then per
  discovered answer, port `question_instances` (substitute the answer's
  bindings in first-occurrence variable order; flip the sign for the
  negation) and run the pairing pass over the same worlds: re-generate
  world `t`, decide the closed positive instance (for a closed question,
  reuse the phase-1 verdict instead of re-running — port that shortcut)
  and the closed negated instance. Cells pos_only/neg_only/both/neither;
  estimate and CI from `paired_diff_ci`.
- `gkdefault` is NOT offered on the page (menu stays small); do not port it.

Answer keys must match between phase 1 and gk's reference run: gk's own
answers from run A are parsed from the same JSON shape (`true` → `"yes"`,
`$ans` values joined), so the final table can join sampled and exact rows
by key.

### 4.5 Statistics (small ports)

`wilson(k, n)` and `paired_diff_ci(pos_only, neg_only, n)` exactly as in
gkmc.py. Display estimates to 3 decimals, intervals to 3 decimals.

### 4.6 Threshold mode (port of threshold_worlds.py)

Port `evaluate()` and its supporting analysis completely: directional
clause reading, noisy-or pooling of same-side testimonies per ground atom,
blockers (`$block` fires on the blocked side's availability), dependency
ordering with least-fixpoint evaluation of one-sided positive cycles, and
every `not_scored` refusal (cycle through a blocker or contested atom,
mutual-block priorities at unequal strengths). Do not simplify these away:
declining is part of the method.

Pool input: the same grounded pool from 4.1 (the Python version grounds
original statements instead; for the accepted fragment — directional
clauses, one conclusion literal, marked by `@head` in the export — the
clause sets are equivalent, and the harness confirms it per example).
`@head` gives the conclusion literal index (facts 0, marker-less rule
clauses -1 → refuse those as Python's directional check does). The query
must be ground and single-literal; otherwise refuse with the threshold
refusal text.

Trials: fixed 100,000 draws regardless of the trials menu (pure JS, well
under a second; the fixed count keeps the display stable). Compare against
run A's `detail` masses in the result table.

## 5. Eligibility checks and refusal texts

Checked in the setup worker after clausification, before any sampling; on
failure reply `{ok:false, refusal}` and the page prints the refusal in the
result area, prefixed `sampling not run: `. Exact texts:

| condition | refusal text |
|---|---|
| the active example preset has `background` or `taxonomy` set (checked page-side before spawning) | `sampling not run: this example uses a large background knowledge base; sampling is limited to small self-contained inputs. Pick one of the confidence examples or write your own.` |
| a nested function term in any clause | `sampling not run: the input uses function terms (nested terms as arguments), which sampling does not support.` |
| a `$`-prefixed predicate other than `$block`/`$not`/`$ans`, or an equality/inequality literal | `sampling not run: the input uses arithmetic, equality or another built-in, which sampling does not support.` |
| no goal clause found | `sampling not run: no query found in the input.` |
| goal reconstruction leaves more than one literal | `sampling not run: sampling supports single-literal questions only.` |
| ground pool over 100,000 clauses | `sampling not run: grounding this input produces over 100,000 clauses; sampling is limited to small inputs.` |
| `gk_clauses_v1` header missing / clausify output unparseable | `sampling not run: could not obtain clauses from gk (unexpected clausifier output).` |
| threshold mode, query not ground | `sampling not run: the four-mass estimate needs a question without variables.` |
| threshold mode, non-directional clause (`@head` -1 or several positive literals) | `sampling not run: the four-mass estimate accepts only directional rules with a single conclusion.` |
| threshold mode, not-scored case at evaluation time | `four masses not scored for this input: <reason from the port, e.g. "a dependency cycle passes through a blocker">.` |

The last row is a result, not an error: render it in the normal result area
without the `sampling not run:` prefix.

## 6. User interface

### 6.1 The sampling row

A new row inside `#advanced_buttons`, directly under the existing
seconds…confidence-limit row (i.e. between the `confidence` input's closing
tag and the `<p>` before the strategy textarea). Exact HTML, matching the
existing inline-block label pattern:

```html
<div style="padding-top: 15px;">
  <div style="display: inline-block; width: 62px; text-align: center;">sampling</div>
  <select class="form-control" style="width: 160px;" id="mc_method">
    <option value="subtract">net confidence</option>
    <option value="provable">provability</option>
    <option value="threshold">four masses</option>
  </select>
  <div style="display: inline-block; width: 50px; text-align: center;">worlds</div>
  <select class="form-control" style="width: 90px;" id="mc_trials">
    <option value="300">300</option>
    <option value="1000" selected>1000</option>
    <option value="10000">10000</option>
  </select>
  <button onclick="useSampling(this); return false;"
    class="btn btn-small btn-primary" style="width: 80px; margin-left: 10px;">Sample</button>
  <a href="#samplingModal" data-toggle="modal" style="margin-left: 12px;">what sampling checks</a>
</div>
```

Behavior:

- **Sample** takes the current text box content and the selected method and
  count, terminates any running solve or sampling, and starts the run.
  The `seconds` field applies to the reference run; world runs keep their
  fixed 2-second cap. The other Advanced controls (detail, print level,
  max answers, confidence limit, strategy) do not affect sampling.
- **Stop** (the existing button next to Solve): extend `stopSolve` to also
  terminate all sampling workers and print `stopped.`.
- Starting a Solve likewise terminates a running sampling (extend `useGk`'s
  entry to call the sampling teardown).
- `resetAdvanced()` resets `mc_method` to `subtract` and `mc_trials` to
  `1000`.

### 6.2 Progress display

Rendered via `showResult` (the normal result area), updated from worker
progress messages:

- during setup: `sampling: preparing (reference run and grounding)...`
- during phase 1: `sampling: 250 / 1000 worlds decided...`
- during pairing: `sampling: checking the negation of answer b: 250 / 1000 worlds...`
- threshold mode finishes too fast to need progress.

### 6.3 Result rendering

Final output replaces the progress text. A heading line, an HTML table, a
one-line method reminder, and a validity line. Numbers to 3 decimals.

Net confidence / provability, exact shape (example values):

```
Sampling check: net confidence, 1000 sampled worlds.

answer   provable   negation provable   net (sampled)   95% interval    gk reports
b        0.905      0.000               0.905           0.887 to 0.923  0.9
a        0.100      0.900               -0.800          -0.837 to -0.763  -0.8

Each world keeps an uncertain statement with probability equal to its
confidence and drops it otherwise; a plain proof search then decides the
world. Valid worlds: 1000, timeouts: 0.
```

For provability the `negation provable` and `net` columns are omitted and
the sampled column is named `provable (sampled)`. Answers reported by gk
but never proved in any world get a `0.000` row (as gkmc prints); answers
sampled but absent from gk's report leave the `gk reports` cell empty.

Four masses, exact shape:

```
Sampling check: four masses, 100000 draws.

                 sampled   gk reports
support for      0.298     0.3
support against  0.000     0
conflict         0.404     0.4
ignorance        0.298     0.3

One random acceptance threshold per ground atom; evidence counts only if
its combined confidence clears the threshold, the same threshold for both
sides. Compare with the detail report of an ordinary solve.
```

The `gk reports` column comes from run A's `detail` block of the answer
matching the query (threshold mode has a single ground query). If run A
reports no answer for the query (e.g. `no information`), leave the column
empty.

Implementation note: build the tables as HTML (`<table class="table
table-condensed">` markup is already used on the page) inside the result
div; do not print markdown.

### 6.4 Warnings

Pool warnings from 4.1 (multi-clause uncertain statement) are appended
under the table in the same result block, prefixed `note: `, e.g.:

`note: statement frm_4 (confidence 0.9) splits into 3 clauses; each ground
clause is kept or dropped by its own draw.`

### 6.5 The modal

New modal `samplingModal`, same structure and styling as the four existing
modals, inserted after `defaultsModal`. Title: `Checking results by
sampling`. Body, exact text:

```html
<p>gk computes its confidences by rules applied to proofs (see <i>how
confidences combine</i>). Sampling checks such numbers against a concrete
reading: treat each confidence as the probability that the statement holds,
generate many random worlds accordingly, and count what happens.</p>
<ul>
<li><b>Provability</b> and <b>net confidence</b> build each world by keeping
every uncertain statement with probability equal to its confidence and
dropping it otherwise; certain statements are always kept. A plain proof
search with no confidence arithmetic then decides the world.
<i>Provability</i> is the fraction of worlds in which the answer is
provable. <i>Net confidence</i> subtracts the fraction in which the
answer's explicit negation is provable, measured in the same worlds &mdash;
mirroring how gk weighs evidence against an answer. One proof search runs
per world in your browser, so thousands of worlds take up to a few
minutes; the 95% interval in the result shows the sampling precision.</li>
<li><b>Four masses</b> estimates the split shown by the detail report:
support for, support against, conflict and ignorance. Each ground atom
draws one random acceptance threshold between 0 and 1; a piece of evidence
counts only if its combined confidence clears the threshold, and the same
threshold applies to the evidence for and against the atom. This mode runs
no proof search and finishes immediately, but accepts a narrower class of
inputs: a question without variables and rules with a single conclusion.</li>
</ul>
<p>The sampled number and gk's number often agree, and agreement supports
the probability reading of that example. They can also differ for
understood reasons: gk may net the evidence on a contested premise before
using it, while sampling counts the worlds in which the premise is provable
(the <i>contested premises</i> example shows this); a recursive rule can
succeed through many different sampled paths while gk reports the evidence
of a selected proof; and defaults with priorities are sampled only in the
documented cases. A difference is a property of the example worth
understanding, not a malfunction.</p>
<p>Sampling needs a small, finite input: constants only, no function terms,
no arithmetic or equality, no background knowledge base. Most of the
confidence examples qualify (examples 2&ndash;12, 15, 16, 19). The method
and its limits are described in the
<a href="https://github.com/tammet/gkreasoner/tree/master/montecarlo">montecarlo
directory</a> of the gkreasoner repository; the estimates are repeatable
&mdash; the same input and world count give the same sampled worlds.</p>
```

### 6.6 The modelinks line

Extend the `More about this:` paragraph with one entry, before the syntax
link:

```html
<a href="#samplingModal" data-toggle="modal">checking by sampling</a> &middot;
```

No other page text changes: no intro paragraph edits, no per-example note
edits, no navbar changes.

## 7. Verification

### 7.1 Reference values (one-time, native)

Generate expected values with the Python reference on the eligible page
examples. Page examples are GKP; convert with the native binary:
`/opt/gkreasoner/bin/gk EX.gkp -writejson > EX.js`, then
`python3 /opt/gkreasoner/montecarlo/gkmc.py -n 10000 --seed 1 EX.js` (and
`--semantics threshold` where the fragment allows). Record the resulting
numbers as the expectations inside `mc_check.js`. Respect the machine
limit: at most 4 concurrent gk processes (`--jobs 4`).

Note the known, intended disagreements with gk's own numbers — e.g.
example 7 (contested premises): sampling gives ≈0.46 where gk reports 0.27.
The harness compares JS sampling against the **Python sampling** values,
not against gk, except where README/comparison.md state agreement.

### 7.2 Node harness `mc_check.js`

Pattern of `commonsense_check.js`: a parent that spawns one child per
example (fresh process = page isolation), children driving `mcsampler.js`'s
logic through the same code paths the page uses (require the worker file
with a small `self`/`importScripts` shim, or factor the pure logic so both
the worker and the harness can load it — prefer the shim; keep one source
of truth). For each eligible example (2–12, 15, 16, 19):

- run setup, assert eligibility verdict matches the table in section 5
  (also assert the *ineligible* examples 13, 14, 18, 20, 23 refuse with the
  right message — skip 21/22, whose ineligibility is decided page-side by
  preset);
- run inclusion sampling at n=1000 seed 0, assert the estimate's 95%
  interval overlaps the recorded Python 10000-trial interval;
- run threshold at 100,000 draws where applicable, assert each mass within
  0.01 of the recorded Python value, and assert the not-scored cases
  refuse/decline identically;
- assert the `gk reports` values parsed from run A equal the confidences
  the ordinary solve prints (spot-check against `commonsense_check.js`
  expectations where they exist).

Run with `/opt/gkcjs/emsdk/node/12.18.1_64bit/bin/node`. The harness must
pass fully before the page work is called done. Keep runtime reasonable:
n=1000 for inclusion in the harness (roughly 1–2 minutes per open-query
example single-threaded; run examples sequentially).

### 7.3 Browser checks

With a local serve or the live page after deploy, verify by hand (or with
the Chrome extension if connected):

1. example 3, net confidence, 1000 worlds → sampled ≈0.8, gk reports 0.8;
2. example 4, four masses → ≈0.3/0/0.4/0.3 matching the detail report;
3. example 7, net confidence → sampled ≈0.46 vs gk 0.27, and the modal
   paragraph explains why;
4. example 10 (open query, two answers) → two rows, pairing progress text
   appears, signs correct;
5. example 13 (arithmetic) and 21 (background KB) → the exact refusal
   texts;
6. Stop during a 10000-world run stops promptly; a following Solve works;
   a following Sample works (fresh workers);
7. Solve during sampling cancels the sampling;
8. progress updates keep the page responsive; no console errors;
9. run example 3 sampling twice → identical numbers (fixed seed).

## 8. Commits and rollout

Three commits on logictools master, in this order, each leaving the page
functional:

1. `mcsampler.js` + page coordinator + sampling row + inclusion sampling
   (subtract + provable), with `mc_check.js` covering it;
2. threshold mode + its checks;
3. the modal, modelinks entry, and final text polish.

Do not push or pull the server without being asked. The commonsense tab
stays out of the top menu; the page is reachable directly at
/commonsense.html for testing.

## 9. Implementation notes (2026-07-21, as built)

The plan was followed; the points below record where the built version
differs from it, and why. Files: `mcsampler.js` (worker), the sampling block
in `commonsense.html`, `mc_check.js` + `mc_check_ref.json` (harness).

1. **Two ground pools, not one.** Section 4.6 assumed the threshold model
   could reuse the inclusion pool. The reference implementations ground
   differently and both conventions matter: `gkmc.ground_pool` takes the
   constants of every clause including the goal and keeps clause order,
   while `threshold_worlds.ground_clausified` takes the constants of the
   non-goal clauses only (gk's own `dw_collect_constpool` parity) and
   reorients each clause so its implied literal is last. Both are ported
   as they stand, and the setup reply carries the threshold pool separately.
2. **Named blocker priorities are refused for the four masses only.** In the
   clause export both `tax(bird)` and a bare name appear as `["$", name]`.
   Inclusion sampling hands blockers back to gk unchanged in every world, so
   it accepts them; the four-mass model compares priorities itself and
   cannot, so it declines (`REFUSE.namedpriority`). The plan had one
   taxonomy row covering both modes.
3. **The `pair` message carries the question and the answer's bindings**
   instead of ready-made positive and negated instances, so
   `questionInstances` exists once, in the worker.
4. **Which page examples qualify.** Measured, not assumed: 1&ndash;11 and
   15&ndash;19 sample; 12 uses function terms (the plan listed it as
   eligible), 13 arithmetic, 14 equality, 20 function terms, 21&ndash;23 a
   background knowledge base or the taxonomy. The GKS and TPTP notation
   examples (17, 18) sample normally, which the plan did not expect. The
   modal text names the measured set.
5. **The four masses cover a little more than the Python CLI.** That CLI
   grounds the original statements and refuses compact connectives, so it
   declines example 19 (`=>`); the clause export has already removed them,
   so the browser scores it. Verified against gk's own detail report
   instead of a Python reference for that one example.
6. **Confidences are per-clause and post-split**, as section 4.1 specified.
   A statement splitting into k clauses is drawn per clause, and the note
   names both the drawn value and the stated product (`0.8944` each,
   `0.8` together). gkmc.py instead reuses the unsplit number for every
   clause, so the two tools differ on such inputs; the browser agrees with
   gk's own reading there.
7. **Rejected answers are shown.** gk reports answers defeated by exceptions
   in a separate list; they are joined into the table and marked
   `1 (rejected)` in the *gk reports* column, so an answer that sampling
   proves in some worlds is never left with an empty cell.
8. **A gk memory bug forced a worker-lifecycle addition.** `Main/gk.c` (gk
   1.0.2) returns early from the proving path when an open question ends
   with no answers at all — the `!okanswers && parse_question_type == 2`
   branch — and that single return skips the `#ifdef __EMSCRIPTEN__` block
   at the end of the same function that frees the database. Every other exit
   frees it, so thousands of consecutive world runs are otherwise fine, but
   a world that takes this path leaks its whole database: at the 100 MB
   WebAssembly default the module dies on the 6th such world, at `-mbsize 20`
   on the 29th (measured; the retained amount is proportional to the
   database size). Examples 11, 15 and 18 hit it.
   The plan forbids changing gk, so the worker copes instead: world runs ask
   for a 20 MB database, the worker counts the worlds that took the leaking
   path, and at 20 of them it hands the rest of its job back unfinished. The
   page then replaces that worker and continues the range where it stopped,
   which is invisible in the result (example 11 at 1000 worlds: 0 timeouts).
   `Module.onAbort` is the backstop if some other input exhausts memory
   faster, and a database-too-small error stops the run with its own message
   rather than being counted as a timeout. **A one-line gk fix (adding the
   existing cleanup to that return) would remove the need for all of this**;
   the recycling would then only be a safety net and `LEAK_LIMIT` could be
   raised.
9. **The per-world generator was measured, not assumed.** Section 3.3 seeds
   one mulberry32 per world from an FNV-1a hash of `"<seed>:<trial>"`, and
   consecutive trial numbers give arithmetically related hashes, which some
   small generators do not mix away. Taking the k-th draw of n worlds for
   k = 1..8, eight probabilities and 120 seed sets (7680 cells), the observed
   frequencies are ideal: mean z = 0.007 and mean |z| = 0.800 against the
   ideal 0.798 at n = 300, with the largest single cell at 3.8 as expected
   for that many cells. Adding a splitmix avalanche or a warm-up changed
   nothing measurable, so the plain seeding stands.
10. **Verification.** `mc_check.js` runs every example listed above at 1000
   worlds against `mc_check_ref.json` (gkmc.py at 4000 trials,
   threshold_worlds.py at 100000 draws, seed 1), by interval overlap for
   inclusion and 0.01 absolute for the masses, plus the refusal texts.
   The browser checks of section 7.3 were run headlessly in real Chrome
   (real workers, real wasm) with a scripted page, since the interactive
   extension was not connected: examples 3, 4, 7, 10, 13, 21, the Stop and
   Solve-during-sampling cases, and a repeat run giving identical numbers.

## 11. Out of scope (do not do)

- No changes to gk/gkc C sources, no `-mc` flag, no wasm rebuild, no
  version bumps.
- No `gkdefault` semantics, no shared-draws UI, no seed UI, no
  `--classify` table.
- No sampling for the background-KB or taxonomy examples.
- No new external libraries, no build step: plain JS files served as-is.
- No deletion or renaming of existing files.
