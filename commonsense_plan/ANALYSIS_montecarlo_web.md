# Adding the gkreasoner Monte-Carlo methods to commonsense.html

Analysis, 2026-07-21. Question: can the sampling calculations in
/opt/gkreasoner/montecarlo run on the public page, preferably on the
existing examples and on user input? Is calling the wasm solver per trial
fast enough, and does the browser survive thousands of calls? Alternative:
build the sampling loop into gk itself.

All timings below were taken with the exact gkjs.js/gkjs.wasm (gk 1.0.2,
1000MB) deployed on the page, run under node 12 (the emsdk one; browser
engines are the same generation of V8/SpiderMonkey or newer, so these are
conservative).

## What the two methods need

1. **Inclusion sampling** (`gkmc.py`, semantics subtract/provable/gkdefault):
   clausifies the input once, grounds the clauses over the constants in the
   file, then per trial keeps each uncertain ground clause with probability
   equal to its confidence and asks gk, as a plain Boolean oracle
   (`-nonegative -plain`), whether the answer and its negation are provable.
   Cost model: 1–5 gk runs per trial (closed query, subtract: 2; open query:
   plus 2 per discovered answer). Default 10,000 trials.

2. **Threshold sampling** (`threshold_worlds.py`): estimates the four masses
   (support_for / support_against / conflict / ignorance) with one random
   threshold per ground atom. Runs **no gk at all**; it is a self-contained
   evaluation over the grounded clauses.

## Measurements

Repeated `callMain` on ONE wasm module instance (the design question:
does gk's state survive re-runs, and does memory leak?):

| test | result |
|---|---|
| module init (per worker, one-time) | 130–200 ms |
| trivial 1-clause world, `-nonegative -plain` | 18 ms/call |
| bird_exception world (blockers, open query) | 55 ms/call |
| 2000 consecutive calls, one instance | all succeed, no slowdown (17→28 ms range), RSS flat at 114 MB |
| `-mbsize 20` vs default | no difference (cost is parse + db format + print, not db size) |
| 4 concurrent instances, 250 calls each | 16 s wall for 1000 world decisions; ~3.4× throughput |
| `-defworlds -clausify -outformat json` in wasm | works, ~20 ms, on GKP input too |

Conclusions from the numbers:

- **Reuse is safe.** gk frees its database when main returns; one module
  instance inside a Web Worker can decide thousands of worlds. The
  static-globals leak between `callMain` calls (the reason the interactive
  page uses a fresh worker per solve) is harmless here because every trial
  uses identical flags.
- **The browser survives easily** — provided the trials reuse one instance
  per worker. What would NOT work is a fresh Worker (or fresh module) per
  trial: ~8–12× slower (init dominates) and thousands of 1000MB-heap
  instantiations for nothing.
- **The per-call floor is overhead, not solving.** Deciding a 1-clause world
  natively takes microseconds; the 18 ms floor is input parse + database
  format + output print repeated per call. This is exactly what an in-C
  sampling loop would remove.
- `-defworlds -clausify -outformat json` returns the `gk_clauses_v1` export
  (per-clause confidences, goal marking, JSON-array clause syntax) for ANY
  input syntax the page accepts (GKP/JSON/GKS/TPTP). So the JS port needs no
  parser of its own — one wasm call replaces `load_original` + `clausify`.

## Projected user-facing times (inclusion sampling, subtract)

Closed query ≈ 2 gk runs/trial at 20–60 ms each:

| trials | 95% CI half-width | 1 worker | 4 workers |
|---|---|---|---|
| 300 | ~0.06 | 12–36 s | 4–10 s |
| 1,000 | ~0.03 | 40 s – 2 min | 10–35 s |
| 10,000 | ~0.01 | 7–20 min | 2–5 min |

Open queries multiply this by the number of discovered answers (bird_exception:
up to 5 runs/trial). Threshold sampling is not in the table: 10,000 trials of
the JS port will finish well under a second, with no wasm calls.

## Which page examples qualify

The sampling limits (finite constant domain, no function terms, no
arithmetic/equality/builtins) admit exactly the confidence-flavored examples:

- **Eligible:** 2–12 (confidences … a story), 15 (conflict detail),
  16 (JSON notation), 19 (defaults in JSON). Also user input within the
  same limits — the port must keep gkmc's clean refusals for the rest.
- **Excluded:** 1 (nothing uncertain — would trivially return 1.0),
  13 (arithmetic), 14 (equality), 17–18 (notation demos, 18 has arithmetic),
  20 (function terms in plans), 21–22 (background KB: grounding over all KB
  constants blows up the pool), 23 (taxonomy-valued priorities).
- Threshold mode accepts a narrower fragment still (ground single-literal
  query, directional clauses) — roughly examples 2–11, 15, 16, 19.

## Recommended architecture (JS orchestration + wasm oracle)

A new `mcworker.js` per sampling session (terminated by Stop, like the
solve worker), or N of them for parallelism:

1. One call `["input", "-defworlds", "-clausify", "-outformat", "json"]`
   → clause list with confidences.
2. Ground the pool in JS — a port of `ground_pool` (~150 lines; the
   name-run mapping and its safety check must be ported as-is).
3. Trial loop: seeded PRNG picks the world, `FS.writeFile("input", ...)`,
   `callMain(["input","-nonegative","-plain"])`, parse the answer lines.
   Same-flag reuse of one instance per worker.
4. Aggregate in JS (Wilson / paired-difference CI, direct ports).
5. Post progress every ~25 trials; the page shows a running estimate ± CI
   next to gk's own confidence; optional early stop when the CI is narrow
   enough.

Threshold mode runs entirely inside the same worker with no wasm calls
(port of threshold_worlds.py, ~700 lines of straightforward JS).

Deterministic seeds (`seed:trial` string hash, as in Python) keep browser
results reproducible and comparable with the Python reference.

Estimated new code: ~150 lines grounding, ~200 lines trial loop + stats,
~700 lines threshold port, ~200 lines UI (an "Estimate by sampling" control
with semantics + trial-count choices, running estimate, stop).

## Alternative: build the sampling loop into gk

Add `-mc N -seed S` so one gk run does clausify + ground + N world decisions
internally and prints the table.

- Feasible: gk already re-runs the reasoner several times in one process
  (the strategy ladder), so per-run state reset exists. New C work: ground
  pool construction, inclusion draws, the paired negation runs, aggregation
  — roughly 1–2k lines.
- Gain: removes the 18–55 ms per-call overhead; est. 1–10 ms per trial, so
  10,000 trials in tens of seconds of wasm, single-threaded. Also usable
  from the command line, replacing the Python orchestration.
- Cost: the largest development and testing effort of the options; the
  sampling semantics carry documented traps (per-instance vs shared draws,
  per-answer closed instances in contradictory worlds, the name-run
  mapping); bugs go into the core binary and force releases. The Python
  scripts would become the test reference.
- The methods are documented as diagnostic tools independent of gk's
  confidence arithmetic. Inclusion mode keeps that property either way
  (gk stays a plain Boolean oracle per world), but the separation is easier
  to explain when the orchestration is visibly outside gk.

## Recommendation

Staged:

1. **Threshold sampling in JS** — no wasm calls, instant results, smallest
   effort. Immediately gives the four-mass comparison on most confidence
   examples.
2. **Inclusion sampling via worker + module reuse** — default 300 trials
   ("quick estimate", seconds), options 1,000 and 10,000 with progress bar
   and Stop; 2–4 parallel workers on `navigator.hardwareConcurrency`.
   The measurements above show this is comfortably viable.
3. **`-mc` inside gk only if needed later** — if real usage wants 10,000+
   trials routinely, the in-C loop is the 5–20× step. The page architecture
   barely changes (one wasm call instead of a loop), so nothing in stages
   1–2 is thrown away.
