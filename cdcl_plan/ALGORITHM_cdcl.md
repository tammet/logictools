# ALGORITHM: design of `proplog_cdcl.js`

> **Implemented, with deviations.** The shipped solver additionally has
> `minimize_learned` (self-subsuming resolution on the learned clause) and
> `reduce_learned` + `watch_clause` (periodic deletion of the longer half of the
> learned clauses, done at decision level 0 after a forced restart) - §9 below
> called these optional, but without deletion the solver loses to plain dpll.
> Tuned constants: `RESTART_BASE=128`, `LEARNED_FACTOR=0.4`,
> `LEARNED_MINIMUM=500`, `LEARNED_GROWTH=1.1`. The `clauses.length===0` early
> return after preprocessing was dropped: letting the main loop assign the
> remaining variables costs nothing and always yields a complete model.

This file fixes the design of the new solver so the implementation needs no
further algorithmic decisions. Read `proplog_dpll.js` side by side with this
file: the new solver is deliberately a modification of it.

References to cite in the file header and section comments:

- https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
- https://en.wikipedia.org/wiki/DPLL_algorithm
- N. Eén, N. Sörensson, "An Extensible SAT-solver" (the MiniSat paper):
  http://minisat.se/downloads/MiniSat.pdf — the classic readable description of
  exactly the techniques used here (watched literals, 1UIP analysis, VSIDS,
  restarts).
- https://github.com/arminbiere/kissat — a modern high-performance CDCL solver
  (for further reading; our code is a teaching-sized version of the same ideas).

## 1. What changes conceptually vs `proplog_dpll.js`

`proplog_dpll.js` does recursive chronological backtracking: pick a variable,
try `true` (recurse), try `false` (recurse), undo. When a clause becomes false
it only bumps variable activities and returns.

CDCL keeps everything false-clause-detection and unit propagation do, but:

1. Search is an **iterative loop** over an explicit **trail** (the sequence of
   assigned literals in assignment order). Recursion disappears.
2. Every propagated literal remembers its **reason clause**; decisions have no
   reason. This turns the trail into an implication graph.
3. On conflict, **conflict analysis** resolves the false clause with reason
   clauses backwards along the trail until only one literal of the current
   decision level remains (the **first unique implication point**, 1UIP). The
   negations of the collected literals form a new **learned clause** which is
   added to the clause set: the search can never repeat this conflict.
4. The learned clause dictates **non-chronological backtracking** (backjumping):
   jump straight back to the second-highest decision level in the learned
   clause, where the learned clause is unit and immediately propagates its
   asserting literal.
5. Variable choice uses **VSIDS-style activities**: bumped during conflict
   analysis, decayed geometrically, so the search focuses on recently
   conflicting variables. (This replaces dpll's ad-hoc "add weight from the last
   contradiction clause".)
6. **Phase saving**: when a variable is unassigned by backjumping, remember its
   last value; the next decision on it tries that value first.
7. **Restarts**: after a scheduled number of conflicts (Luby sequence), jump
   back to decision level 0, keeping learned clauses, activities and saved
   phases. Restarts + learning make the search dramatically more robust.

UNSAT is detected when a conflict occurs at (or a learned unit contradicts)
decision level 0. SAT is detected when all variables are assigned and
propagation finds no conflict.

## 2. Module layout (mirroring `proplog_dpll.js`)

```
header comment (usage, licence, links)            — like proplog_dpll.js
(function(exports){ "use strict";
  // trace + result globals: trace_flag, trace_method, trace_list,
  //                          origvars, result_model
  // statistics globals: conflicts_count, decisions_count,
  //   propagations_count, learned_count, restarts_count, max_level_count,
  //   units_derived_count (level-0 units, incl. preprocessing)
  // solver state globals (created in exports.cdcl):
  //   varvals, varlevel, varreason, varactivities, savedphase, seen,
  //   posbuckets, negbuckets, trail, trailend, qhead, levelstarts,
  //   decisionlevel, activity_inc
  exports.cdcl = function(clauses,maxvarnr,trace,varnames) {...}
  // --- main search loop helpers ---
  function propagate() {...}
  function enqueue(lit,reason) {...}
  function next_decision() {...}          // variable + phase choice
  function analyze(conflclause) {...}     // returns [learnedclause, backlevel]
  function backjump(level) {...}
  function addwatch(lit,clause) {...}
  function bump_activity(varnr) {...}
  function decay_activities() {...}
  function luby(x) {...}
  // --- preprocessing, copied/adapted from proplog_dpll.js ---
  function maxvar_and_meta(clauses) {...}          // copy as-is
  function simplify_clause_list(clauses) {...}     // copy, trimmed (see §5)
  function initial_activities(clauses) {...}       // simplified count_occurrences
  function makebuckets(clauses) {...}              // copy as-is
  // --- output helpers, copied from proplog_dpll.js ---
  function store_model(varvals) {...}
  function print_trace(depth,txt) {...}
  function showvar(x) {...}
  function clause_to_str(cl) {...}
})(this.proplog_cdcl = {});
```

Note: unlike `proplog_dpll.js`, which threads state through function arguments
(a leftover of its recursive shape), the CDCL solver may keep the state arrays
in module-level variables assigned at the top of `exports.cdcl` — the iterative
loop makes this natural and the code much more readable. Every state global MUST
be (re)initialized inside `exports.cdcl` so repeated calls are independent.

## 3. Data structures

All indexed by variable number `1..maxvarnr` unless said otherwise.

| name            | type                | meaning |
|-----------------|---------------------|---------|
| `varvals`       | `Int32Array`        | 0 unassigned, 1 true, -1 false (same as dpll) |
| `varlevel`      | `Int32Array`        | decision level at which the var was assigned |
| `varreason`     | `Array`             | reason clause (the clause object) for propagated vars; `0` for decisions and level-0 facts |
| `varactivities` | `Array` of numbers  | VSIDS activity (float; grows, gets rescaled) |
| `savedphase`    | `Int32Array`        | 1 or -1: last value the var had; initialized to 1 (so the first decision tries `true`, like dpll splitting positively first) |
| `seen`          | `Int32Array`        | scratch flags for conflict analysis, always left all-zero between calls |
| `trail`         | `Int32Array(maxvarnr+1)` | assigned literals in assignment order |
| `trailend`      | int                 | number of used trail slots |
| `qhead`         | int                 | next trail index to propagate (`qhead<=trailend`) |
| `levelstarts`   | `Array` of ints     | `levelstarts[l]` = trail index where decision level `l` begins; `levelstarts[0]=0`; `decisionlevel===levelstarts.length-1` |
| `posbuckets`, `negbuckets` | as in dpll | per-variable watch lists: `bucket[0]`=count, clauses at `1..count` |

Clause representation is EXACTLY that of `proplog_dpll.js`: an `Int32Array`
whose slots `[0]` and `[1]` hold the two watched literals and whose literals
start at index 2. Learned clauses are built in the same shape, so
`clause_to_str` and the propagation code work on them unchanged.

`activity_inc` (float, starts at 1) is the current bump amount;
`ACTIVITY_DECAY = 0.95` and `ACTIVITY_RESCALE = 1e100` are constants.

## 4. Functions in detail

### exports.cdcl(clauses, maxvarnr, trace, varnames)

```
set/clear trace globals and statistics exactly like proplog_dpll.dpll does
[maxvarnr, clauses] = maxvar_and_meta(clauses)
allocate all arrays (see §3)
clauses = simplify_clause_list(clauses)          // may set varvals for units
if clauses===false: trace "contradiction found during simplification";
                    return [false, joined trace]
if clauses.length===0: store_model(varvals); return [model, joined trace]
initial_activities(clauses)                       // occurrence-count seeds
makebuckets(clauses)
// put the units found by preprocessing on the trail as level-0 facts:
decisionlevel=0; levelstarts=[0]; trailend=0; qhead=0
for v in 1..maxvarnr where varvals[v]!==0:
    trail[trailend++] = v*varvals[v]; varlevel[v]=0; varreason[v]=0
// main CDCL loop:
conflicts_until_restart = RESTART_BASE * luby(restarts_count)     // RESTART_BASE=64
loop forever:
    confl = propagate()
    if (confl !== 0) {                            // conflict found
        conflicts_count++
        if (decisionlevel === 0) { final stats trace; return [false, joined trace] }
        tmp = analyze(confl)                      // [learned_lits_array, backlevel]
        backjump(tmp[1])
        install_learned(tmp[0])                   // see below; enqueues asserting lit
        decay_activities()
        if (conflicts since last restart >= conflicts_until_restart) {
            restarts_count++
            trace "restart"
            backjump(0)
            conflicts_until_restart = RESTART_BASE * luby(restarts_count)
        }
    } else {                                      // no conflict
        lit = next_decision()
        if (lit === 0) {                          // all vars assigned: SAT
            store_model(varvals); final stats trace; return [model, joined trace]
        }
        decisionlevel++; levelstarts.push(trailend)
        if (decisionlevel > max_level_count) max_level_count = decisionlevel
        enqueue(lit, 0)
        trace "decision"
    }
```

Final statistics line, in the dpll style, e.g.:
`"search finished: conflicts N, decisions N, propagations N, learned clauses N, restarts N, max level N"`.

`install_learned(lits)` (may be inlined in the loop, but keep it a named helper
for readability): `lits[0]` is the asserting literal (see `analyze`).

```
learned_count++
if (lits.length === 1):
    units_derived_count++
    enqueue(lits[0], 0)                 // we are at level 0 after backjump
else:
    build clause = Int32Array(lits.length+2):
        clause[0]=lits[0]; clause[1]=lits[1]      // watches: asserting lit +
                                                  // a literal from the backjump level
        clause[2..]=lits
    addwatch(lits[0], clause); addwatch(lits[1], clause)
    enqueue(lits[0], clause)
trace "learned clause (...), backjumping to level L"
```

Watching `lits[0]` (asserting) and `lits[1]` (highest remaining level — `analyze`
guarantees this placement) preserves the watched-literal invariant: after any
future backtrack past this point, these two are the last literals of the clause
to become false.

### propagate() → conflicting clause or 0

The heart, adapted from `unit_propagate` of `proplog_dpll.js` (keep the clever
in-place bucket compaction; change what happens on unit and on conflict):

```
while (qhead < trailend):
    dlit = trail[qhead++]; propagations_count++
    negdlit = -dlit
    bucket = (dlit<0) ? posbuckets[-dlit] : negbuckets[dlit]   // clauses watching ~dlit
    bucketlen = bucket[0]
    for i in 1..bucketlen:                       // same loop shape as dpll
        clause = bucket[i]
        // find the other watched literal:
        otherw = (clause[0]===negdlit) ? clause[1] : clause[0]
        if (value_of(otherw) === true): continue // clause already satisfied
        // scan clause body for a non-false replacement literal
        // that is not the other watch:
        found = 0
        for j in 2..clause.length-1:
            lit = clause[j]
            if (lit !== otherw && value_of(lit) !== false): { found=lit; break }
        if (found):
            // move the watch from negdlit to found:
            if (clause[0]===negdlit) clause[0]=found else clause[1]=found
            addwatch(found, clause)
            // remove from current bucket exactly like dpll:
            bucket[i]=bucket[bucketlen]; bucket[0]--; bucketlen--; i--
            continue
        // no replacement: clause is unit or false under otherw
        if (value_of(otherw) === false):
            return clause                        // CONFLICT
        enqueue(otherw, clause)                  // unit: propagate with reason
        trace "derived otherw from clause (...)"
return 0
```

`value_of(lit)` is the tiny inline pattern used all over dpll
(`lit<0 ? -varvals[-lit] : varvals[lit]` compared against 1/-1/0) — write it
inline with the sign/polarity idiom of the existing code rather than as a
function call, matching the house style.

### enqueue(lit, reason)

```
nr = |lit|; varvals[nr] = sign(lit); varlevel[nr] = decisionlevel
varreason[nr] = reason; trail[trailend++] = lit
```
(Callers guarantee the variable is currently unassigned.)

### next_decision() → literal or 0

Linear scan for the unassigned variable with maximal activity, exactly like
dpll's `next_var` (comment: real solvers use a heap; O(n) is fine and readable
here). Return `bestvar * savedphase[bestvar]`, or 0 if none unassigned.
Increment `decisions_count`.

### analyze(confl) → [lits, backlevel]

Standard first-UIP conflict analysis. Returns `lits` (a plain js array of the
learned clause's literals with the asserting literal at index 0 and, when
`lits.length>1`, a literal of the backjump level at index 1) and `backlevel`.

```
lits = [0]                     // slot 0 reserved for the asserting literal
counter = 0                    // vars of current decision level not yet resolved
lit = 0; index = trailend - 1
c = confl
do:
    // c is the clause being resolved into the running result;
    // on the first pass process ALL its literals, on later passes skip
    // slot of the resolved-upon literal (see loop below: we simply skip
    // literals whose var is the var of `lit`)
    for j in 2..c.length-1:
        q = c[j]
        v = |q|
        if (!seen[v] && varlevel[v] > 0):
            seen[v] = 1
            bump_activity(v)
            if (varlevel[v] === decisionlevel) counter++
            else lits.push(q)                  // stays in the learned clause
    // pick the next current-level literal to resolve on:
    while (!seen[|trail[index]|]) index--
    lit = trail[index]; index--
    seen[|lit|] = 0
    counter--
    c = varreason[|lit|]
while (counter > 0)
lits[0] = -lit                                 // the 1UIP, negated
// clear remaining seen flags:
for each q in lits: seen[|q|] = 0
// compute backjump level and put a max-level literal at slot 1:
if (lits.length === 1): backlevel = 0
else:
    find k>=1 maximizing varlevel[|lits[k]|]; swap lits[1] and lits[k]
    backlevel = varlevel[|lits[1]|]
return [lits, backlevel]
```

Why `varlevel[v] > 0` skips level-0 vars: literals false at level 0 are false
forever, so they would be dead weight in the learned clause — this is the
standard simplification and must be commented.

Note the subtlety that makes the simple `for j in 2..` loop correct: when `c` is
a reason clause of variable `v`, the literal of `v` itself occurs in `c`, but at
that moment `seen[v]` has just been reset to 0 — however its `varlevel` is the
current level and it was already counted; re-adding must be prevented. The
clean standard solution (use it): when iterating a reason clause, skip the
literal whose variable equals `|lit|` (the literal being resolved upon). For the
initial conflict clause `lit===0`, so nothing is skipped. Implement with an
explicit check `if (|q| === |lit|) continue;` at the top of the inner loop —
and explain it in a comment.

The educational comment before this function must include a small worked
example showing a genuine multi-step resolution. A suitable one: decisions `1`
(level 1), then `2` (level 2); clauses `[-2,3]`, `[-3,-1,4]`, `[-3,-4]`.
At level 2 propagation derives `3` from `[-2,3]`, then `4` from `[-3,-1,4]`,
then `[-3,-4]` becomes false. Analysis starts from the conflict clause
`[-3,-4]`: resolving away `4` with its reason `[-3,-1,4]` gives `{-3,-1}`;
one current-level literal (`3`) remains, so `3` is the first UIP and the
learned clause is `[-3,-1]` — the solver backjumps to level 1 (the level of
`-1`), where the learned clause immediately propagates `-3`. Work this example
out step by step in the comment, and verify it by hand while writing (adjust
the clauses if the arithmetic does not come out as described).

### backjump(level)

```
for k = trailend-1 down to levelstarts[level+1]:
    lit = trail[k]; nr = |lit|
    savedphase[nr] = varvals[nr]        // phase saving happens here
    varvals[nr] = 0; varreason[nr] = 0
trailend = levelstarts[level+1]
qhead = trailend
levelstarts.length = level+1
decisionlevel = level
```
(Only called with `level < decisionlevel`; `levelstarts[level+1]` always
exists.) Trace: `"backjumping to level L"` — printed by the caller together
with the learned clause.

### addwatch(lit, clause)

Bounds-checked append (dpll's raw `bucket[++bucket[0]]=clause` relies on
preallocated placeholder slots, which learned clauses don't have):

```
bucket = (lit<0) ? negbuckets[-lit] : posbuckets[lit]
bucket[0]++
if (bucket[0] >= bucket.length) bucket.push(clause)
else bucket[bucket[0]] = clause
```

Use this helper for ALL watch appends, including the watch-move inside
`propagate`.

### bump_activity(v) / decay_activities()

```
bump:  varactivities[v] += activity_inc
       if (varactivities[v] > 1e100):        // rescale to avoid Infinity
           for all vars w: varactivities[w] *= 1e-100
           activity_inc *= 1e-100
decay: activity_inc *= (1/0.95)              // growing the increment ==
                                             // decaying all old activities
```
Comment the classic trick: instead of multiplying every activity by 0.95 after
each conflict, grow the increment — same relative effect, O(1).

### luby(x) → element x (0-based) of the Luby sequence 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...

Use the standard closed form (comment the sequence and cite Luby, Sinclair,
Zuckerman 1993, "Optimal speedup of Las Vegas algorithms"):

```
function luby(x) {
  var k, size, seq;
  for (size=1, seq=0; size < x+1; seq++, size=2*size+1) {}
  while (size-1 !== x) {
    size = (size-1) >> 1;
    seq--;
    x = x % size;
  }
  return Math.pow(2, seq);
}
```
Restart interval = `64 * luby(restarts_count)` conflicts (x is 0-based:
luby(0)=1, luby(1)=1, luby(2)=2, luby(3)=1, ... — verify against the sequence
in a node one-liner before wiring it in).

## 5. Preprocessing: what to copy, what to drop

- `maxvar_and_meta`: copy as-is (adds the two meta slots used as watch
  pointers).
- `simplify_clause_list`: copy essentially as-is (unit
  propagation/subsumption, tautology and duplicate-literal removal before the
  search; sets `varvals` for detected units). Signature may be simplified to use
  the module-level state. Keep its trace output.
- `count_occurrences`: SIMPLIFY into `initial_activities(clauses)` — keep only
  the occurrence-count-with-length-bonus seeding of `varactivities`; DROP all
  the pure-literal machinery (`purevars`, `occvars` polarity tracking, the
  commented-out elimination code, `clean_result`). Rationale to state in a
  comment: pure-literal elimination conflicts with clause learning (learned
  clauses can change polarity balances) and modern solvers do not use it during
  search.
- `makebuckets`: copy as-is; it establishes the watch invariant
  (`clause[0]`/`clause[1]` = first two literals, entered in the respective
  buckets, placeholders appended for the rest).
- Preprocessing-derived units enter the trail as level-0 facts before the first
  `propagate()` call (see the main loop in §4) — this both cleans the buckets of
  satisfied/false-watch clauses and detects immediate UNSAT uniformly, with no
  special-case code.

## 6. Trace format

Indentation depth = current decision level (mirrors dpll's recursion depth).
Reuse `print_trace(depth, txt)` and `showvar` verbatim. Events (all only when
`trace_flag` and meaningful `trace_method`):

- decision: `deciding var X at level L`
- propagation: `derived X from clause (...)` (uses `clause_to_str`)
- conflict: `conflict at level L in clause (...)`
- learning: `learned clause (...), backjumping to level B`
- restart: `restart R after C conflicts`
- final line always appended (even without trace, like dpll):
  the statistics line of §4.

Keep traces cheap: guard every trace-string construction with
`if (trace_flag)`.

## 7. Statistics

Track and print: `conflicts_count`, `decisions_count`, `propagations_count`
(literals propagated, i.e. trail entries processed), `learned_count`,
`restarts_count`, `max_level_count`, `units_derived_count`. Educationally
interesting comparison for the visitor: dpll's "unit propagations count" vs
cdcl's "conflicts".

## 8. Algorithm-level pitfalls

1. **Watch invariant with learned clauses**: the two watched literals of a
   learned clause must be the asserting literal and a literal of the backjump
   level (§4 `install_learned`). Watching two arbitrary literals breaks
   propagation after later backjumps and yields wrong SAT answers — the fuzz
   test will catch it.
2. **`analyze` must skip the resolved-upon literal** when expanding a reason
   clause (see the note in §4), otherwise `counter` is corrupted and the loop
   can terminate early or never terminate.
3. **Level-0 literals never enter learned clauses** (`varlevel[v] > 0` guard).
   Without it, correctness survives, but clauses bloat — implement the guard.
4. **A learned unit clause** means backlevel 0: after `backjump(0)` enqueue it
   as a level-0 fact with reason `0`. Do not try to addwatch a 1-literal clause
   (there is no second watch).
5. **The conflict-at-level-0 UNSAT test must happen before `analyze`** — with
   `decisionlevel===0` there is no UIP and `analyze` would underflow the trail.
6. **`seen` hygiene**: every flag set during `analyze` must be cleared before
   returning (both the resolved-upon vars — cleared inside the loop — and the
   final `lits` — cleared after). A stale flag poisons the next analysis.
7. **`qhead` must be reset to `trailend` on backjump**; forgetting this
   re-propagates stale trail entries.
8. **Do not reuse dpll's conflict-time varvals rollback**: in dpll,
   `unit_propagate` restores `varvals` on conflict; in CDCL, only `backjump`
   unassigns variables. Propagate must leave the trail intact on conflict —
   `analyze` needs it.
9. **Termination**: with learning + restarts the solver terminates because each
   learned clause is new relative to the current trail prefix; do not add
   heuristic "forgetting" of learned clauses (would require restart-progress
   care). Keeping all learned clauses is fine at this site's problem sizes;
   note clause-database reduction as a further-reading comment (MiniSat §4,
   kissat's `reduce.c`).
10. **`savedphase` init to 1** so deterministic behavior matches dpll's
    "positive first" splitting on fresh variables (nice for comparing traces).
