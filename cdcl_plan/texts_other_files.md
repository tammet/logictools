> **Superseded in part.** These texts were applied, except that the wording
> claiming cdcl is simply "the best solver" was replaced by an accurate
> description (cdcl and dpll are on par on random 3-sat, cdcl is the algorithm
> the modern solvers are built on), and the "dpll: better" feature list lost its
> preprocessing bullet, since that preprocessing was unsound and was removed.
> The site files themselves are the authority on the final wording.

# Prepared texts: `proplog_ui.js`, `proplog.html`, `download.html`, `about.html`, `closurecompiler.txt`

Exact OLD → NEW replacement blocks, same conventions as `texts_prop_html.md`.

## §1 `proplog_ui.js`

### 1a — header comment, file list (lines 15–22)

OLD:
```js
    proplog_parse.js
    proplog_convert.js
    proplog_generate.js
    proplog_dpll.js
    proplog_naivedpll.js
```

NEW:
```js
    proplog_parse.js
    proplog_convert.js
    proplog_generate.js
    proplog_cdcl.js
    proplog_dpll.js
    proplog_naivedpll.js
```

### 1b — doc comment of solve (lines 58–59)

OLD:
```js
    solver_algorithm - one of "dpll_better","dpll_naive",
      "truth_table_naive","truth_table_better","resolution_naive","resolution_better"
```

NEW:
```js
    solver_algorithm - one of "cdcl","dpll_better","dpll_old","dpll_naive",
      "truth_table_naive","truth_table_better","resolution_naive","resolution_better"
```

### 1c — the dispatch chain (lines 102–115)

Replaces the whole chain: adds cdcl first and normalizes the accidental
`if`/`else if` mix (two branches restarted the chain with a plain `if`).

OLD:
```js
  if (solver_algorithm=="dpll_better") 
    res=proplog_dpll.dpll(clauses,maxvar,trace_method,origvars);
  if (solver_algorithm=="dpll_old") 
    res=proplog_olddpll.olddpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="dpll_naive")    
    res=proplog_naivedpll.naivedpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="truth_table_naive") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"leaves",trace_method,origvars); 
  else if (solver_algorithm=="truth_table_better") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"nodes",trace_method,origvars); 
  if (solver_algorithm=="resolution_naive") 
    res=proplog_naiveres.naiveres(clauses,maxvar,trace_method,origvars); 
  else if (solver_algorithm=="resolution_better")
    res=proplog_res.resolution(clauses,maxvar,trace_method,origvars); 
```

NEW:
```js
  if (solver_algorithm=="cdcl") 
    res=proplog_cdcl.cdcl(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="dpll_better") 
    res=proplog_dpll.dpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="dpll_old") 
    res=proplog_olddpll.olddpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="dpll_naive")    
    res=proplog_naivedpll.naivedpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="truth_table_naive") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"leaves",trace_method,origvars); 
  else if (solver_algorithm=="truth_table_better") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"nodes",trace_method,origvars); 
  else if (solver_algorithm=="resolution_naive") 
    res=proplog_naiveres.naiveres(clauses,maxvar,trace_method,origvars); 
  else if (solver_algorithm=="resolution_better")
    res=proplog_res.resolution(clauses,maxvar,trace_method,origvars); 
```

## §2 `proplog.html` (the barebones page — loads individual files)

### 2a — script tags (lines 13–14)

OLD:
```html
<script src="proplog_generate.js"></script>
<script src="proplog_dpll.js"></script>
```

NEW:
```html
<script src="proplog_generate.js"></script>
<script src="proplog_cdcl.js"></script>
<script src="proplog_dpll.js"></script>
```

### 2b — selectbox (lines 42–43)

OLD:
```html
    <select style="height: 36px;" id="algorithm_select">
      <option value="dpll_better">dpll: better</option>
```

NEW:
```html
    <select style="height: 36px;" id="algorithm_select">
      <option value="cdcl">cdcl: clause learning</option>
      <option value="dpll_better">dpll: better</option>
```

## §3 `download.html`

### 3a — release date (lines 150–152). Use the actual date of the work.

OLD:
```html
<div style="margin-top: 10px; margin-bottom: 10px;">
Release 2020-08-31.
</div>
```

NEW:
```html
<div style="margin-top: 10px; margin-bottom: 10px;">
Release 2026-07-21.
</div>
```

### 3b — solver file list (lines 164–166): add cdcl first, retitle dpll

OLD:
```html
<ul style="margin-top: 10px;">
<li><a href="proplog_dpll.js">proplog_dpll.js</a> the best solver among the ones provided</li>
<li><a href="proplog_olddpll.js">proplog_olddpll.js</a> old-style dpll: no learning and full pure literal elimination</li>
```

NEW:
```html
<ul style="margin-top: 10px;">
<li><a href="proplog_cdcl.js">proplog_cdcl.js</a> conflict-driven clause learning (CDCL): the best solver among the ones provided</li>
<li><a href="proplog_dpll.js">proplog_dpll.js</a> improved dpll with two watched literals and learned variable weights</li>
<li><a href="proplog_olddpll.js">proplog_olddpll.js</a> old-style dpll: no learning and full pure literal elimination</li>
```

## §4 `about.html`

### 4a — meta keywords (line 10): identical to prop.html Edit 1

OLD:
```html
<meta name="keywords" content="logic, solvers, propositions, dpll, resolution, truth table"> 
```

NEW:
```html
<meta name="keywords" content="logic, solvers, propositions, cdcl, clause learning, dpll, resolution, truth table"> 
```

### 4b — "What does it mean?" best-solver sentence (lines 804–806)

OLD:
```html
You can select and try out several solver algorithms: 
the "<a href='http://en.wikipedia.org/wiki/DPLL_algorithm'>DPLL</a> better" 
is the best solver amongst the options offered on our page. 
```

NEW:
```html
You can select and try out several solver algorithms: 
"<a href='https://en.wikipedia.org/wiki/Conflict-driven_clause_learning'>cdcl</a>: clause learning" 
is the best solver amongst the options offered on our page. 
```

### 4c — "Methods for solving propositional formulas": the DPLL list item (lines 878–918)

Same content change as prop.html Edit 4, but the about.html copy of the block
has slightly different indentation (no two-space lead on the inner list items).
Apply the corresponding replacement:

OLD:
```html
<li><a href="http://en.wikipedia.org/wiki/DPLL_algorithm"><b>DPLL (Davis-Putnam-Logemann-Loveland) search</b></a>
is essentially a constraint solver based on the combination of the truth table search with (limited) 
resolution. For each partial assigment of values in the truth table search we (a) test whether the formula is
already false (like the "truth table: better" method above) and (b) use unit clauses (single literals) to derive new
unit clauses, which is essentially a limited version of resolution.
<p></p>
The DPLL method should be also seen as a general framework: actual solvers implement wildly different
strategies and optimisations. An excellent source for reading about various methods used by the state of the
art solvers is the <a href="http://minisat.se/Papers.html">collection of papers</a> by the authors of 
<a href="http://minisat.se">Minisat</a>, a popular high-end solver. An important extension to DPLL is
<a href="https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning">Conflict-Driven Clause Learning</a>,
currently not implemented by the solvers presented on our page.
<p></p>
We provide three versions of DPLL solvers for experimenting, from worst (and easiest to understand) to 
better and more complicated:
<ul>
<li><a href="proplog_naivedpll.js">dpll: naive</a>
a minimal, naive implementation of dpll with no optimizations. The code is very similar to the 
<a href="proplog_searchtable.js">pure table search solver</a>.</li>
<li><a href="proplog_olddpll.js">dpll: old</a> 
an improved <i>old-style</i> (before the improvements developed in nineties) DPLL. 
It adds the pure literal rule (used after every unit propagation step), selects literals according to weights
calculated before the start of the search, organizes clauses into buckets associated with variables.</li>
<li><a href="proplog_dpll.js">dpll: better</a> implements additional widely used optimizations on
top of the "dpll: old" version (see, for example, 
<a href="http://minisat.se/Papers.html">minisat papers</a> for explanations):
<ul>
  <li>simple preprocessing before search starts: limited unit propagation/subsumption,
    tautology deletion and pure literal deletion</li>
  <li>does not use pure literal rule during search (too time-consuming)</li>    
  <li>learning variable weights: the last contradiction clause adds weights to the variables it contains</li>
  <li>only two literals per clause are watched</li>
</ul> 
However, the important 
<a href="https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning">Conflict-Driven Clause Learning</a>
strategy is not implemented.
</li>  
<p></p>
```

NEW:
```html
<li><a href="http://en.wikipedia.org/wiki/DPLL_algorithm"><b>DPLL (Davis-Putnam-Logemann-Loveland) search</b></a>
is essentially a constraint solver based on the combination of the truth table search with (limited) 
resolution. For each partial assigment of values in the truth table search we (a) test whether the formula is
already false (like the "truth table: better" method above) and (b) use unit clauses (single literals) to derive new
unit clauses, which is essentially a limited version of resolution.
<p></p>
The DPLL method should be also seen as a general framework: actual solvers implement wildly different
strategies and optimisations. An excellent source for reading about various methods used by the state of the
art solvers is the <a href="http://minisat.se/Papers.html">collection of papers</a> by the authors of 
<a href="http://minisat.se">Minisat</a>, a popular high-end solver. The most important extension to DPLL is
<a href="https://en.wikipedia.org/wiki/Conflict-driven_clause_learning">Conflict-Driven Clause Learning</a> (CDCL),
the basis of virtually all modern state of the art solvers: it is implemented on our page as the
"cdcl: clause learning" solver described below.
<p></p>
We provide four versions of DPLL-family solvers for experimenting, from worst (and easiest to understand) to 
better and more complicated:
<ul>
<li><a href="proplog_naivedpll.js">dpll: naive</a>
a minimal, naive implementation of dpll with no optimizations. The code is very similar to the 
<a href="proplog_searchtable.js">pure table search solver</a>.</li>
<li><a href="proplog_olddpll.js">dpll: old</a> 
an improved <i>old-style</i> (before the improvements developed in nineties) DPLL. 
It adds the pure literal rule (used after every unit propagation step), selects literals according to weights
calculated before the start of the search, organizes clauses into buckets associated with variables.</li>
<li><a href="proplog_dpll.js">dpll: better</a> implements additional widely used optimizations on
top of the "dpll: old" version (see, for example, 
<a href="http://minisat.se/Papers.html">minisat papers</a> for explanations):
<ul>
  <li>simple preprocessing before search starts: limited unit propagation/subsumption,
    tautology deletion and pure literal deletion</li>
  <li>does not use pure literal rule during search (too time-consuming)</li>    
  <li>learning variable weights: the last contradiction clause adds weights to the variables it contains</li>
  <li>only two literals per clause are watched</li>
</ul> 
</li>  
<li><a href="proplog_cdcl.js">cdcl: clause learning</a> extends "dpll: better" to a
<a href="https://en.wikipedia.org/wiki/Conflict-driven_clause_learning">Conflict-Driven Clause Learning</a> (CDCL)
solver: the algorithm used, in one form or another, by virtually all modern high-performance SAT solvers
such as <a href="https://github.com/arminbiere/kissat">kissat</a>. On top of the machinery of 
"dpll: better" it adds:
<ul>
  <li>an explicit trail of assignments with a reason clause stored for each propagated variable,
   turning the recursive search of the dpll solvers into an iterative loop</li>
  <li>conflict analysis: each time a clause becomes false, a new <i>learned clause</i> is derived
   by resolution (the <i>first unique implication point</i> method), pinpointing a cause of the conflict
   and guaranteeing the same conflict is never repeated</li>
  <li>non-chronological backtracking (backjumping) guided by the learned clause: the search can
   jump back several decision levels at once</li>
  <li>VSIDS-style variable activities: variables involved in recent conflicts are preferred when
   choosing the next variable to assign</li>
  <li>phase saving: a variable is first tried with the value it was last assigned</li>
  <li>restarts in the Luby sequence: the search is regularly restarted from scratch while keeping
   the learned clauses, activities and saved phases</li>
</ul> 
</li>
<p></p>
```

### 4d — "State of the art propositional solvers" section (after line 943)

OLD:
```html
A good alternative choice is to check out <a href="http://minisat.se">minisat</a>: 
an easily extensible and hackable state of the art solver which is a basis for several
other state of the art solvers. You can even run
<a href="http://www.msoos.org/2013/09/minisat-in-your-browser/">minisat in your browser</a>,
compiled from C to javascript using LLVM.
```

NEW:
```html
A good alternative choice is to check out <a href="http://minisat.se">minisat</a>: 
an easily extensible and hackable state of the art solver which is a basis for several
other state of the art solvers. You can even run
<a href="http://www.msoos.org/2013/09/minisat-in-your-browser/">minisat in your browser</a>,
compiled from C to javascript using LLVM.
<p></p>
The best-known modern conflict-driven clause learning solvers include
<a href="https://github.com/arminbiere/kissat">kissat</a> and
<a href="https://github.com/arminbiere/cadical">cadical</a> by Armin Biere along with their
derivatives, dominating the recent SAT competitions: their source repositories are a good place
to study how a carefully engineered CDCL solver is built. Our own
<a href="proplog_cdcl.js">"cdcl: clause learning"</a> solver is a small educational
implementation of the same core algorithm.
```

Note: about.html has a second, predicate-logic-oriented mention of the SAT
competition around line 620 — leave it unchanged.

## §5 `closurecompiler.txt`

Replace the whole file (the referenced Closure Compiler online service is
retired; the file now documents both the original recipe and the current one):

NEW content of the file:
```
// Historical: proplog_min.js was originally built with the (now retired)
// Google Closure Compiler online service using this recipe:
//
// ==ClosureCompiler==
// @output_file_name proplogic_min.js
// @compilation_level ADVANCED_OPTIMIZATIONS
// @code_url http://logictools.org/proplog_ui.js
// @code_url http://logictools.org/proplog_parse.js
// @code_url http://logictools.org/proplog_convert.js
// @code_url http://logictools.org/proplog_generate.js
// @code_url http://logictools.org/proplog_cdcl.js
// @code_url http://logictools.org/proplog_dpll.js
// @code_url http://logictools.org/proplog_olddpll.js
// @code_url http://logictools.org/proplog_naivedpll.js
// @code_url http://logictools.org/proplog_searchtable.js
// @code_url http://logictools.org/proplog_naiveres.js
// @code_url http://logictools.org/proplog_res.js
// ==/ClosureCompiler==
//
// Current build command (terser; do not pass --toplevel or --mangle-props,
// the modules communicate through this.proplog_* globals):
//
// npx terser proplog_ui.js proplog_parse.js proplog_convert.js \
//     proplog_generate.js proplog_dpll.js proplog_olddpll.js \
//     proplog_naivedpll.js proplog_searchtable.js proplog_naiveres.js \
//     proplog_res.js proplog_cdcl.js \
//     --compress --mangle -o proplog_min.js
```
