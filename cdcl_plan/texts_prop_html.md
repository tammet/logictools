> **Superseded in part.** These texts were applied, except that the wording
> claiming cdcl is simply "the best solver" was replaced by an accurate
> description (cdcl and dpll are on par on random 3-sat, cdcl is the algorithm
> the modern solvers are built on), and the "dpll: better" feature list lost its
> preprocessing bullet, since that preprocessing was unsound and was removed.
> The site files themselves are the authority on the final wording.

# Prepared texts: `prop.html`

Seven edits, given as exact OLD → NEW blocks (whitespace/indentation matches the
current file; use exact string replacement). Line numbers refer to the current
file and are for orientation only.

## Edit 1 — meta keywords (line 10)

OLD:
```html
<meta name="keywords" content="logic, solvers, propositions, dpll, resolution, truth table"> 
```

NEW:
```html
<meta name="keywords" content="logic, solvers, propositions, cdcl, clause learning, dpll, resolution, truth table"> 
```

## Edit 2 — the "using" selectbox (lines 149–150): cdcl first, becomes the default

OLD:
```html
      <select class="form-control" style="width: 180px;" id="algorithm_select">
        <option value="dpll_better">dpll: better</option>
```

NEW:
```html
      <select class="form-control" style="width: 180px;" id="algorithm_select">
        <option value="cdcl">cdcl: clause learning</option>
        <option value="dpll_better">dpll: better</option>
```

## Edit 3 — "What does it mean?" help section, best-solver sentence (lines 342–344)

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

## Edit 4 — "Methods for solving formulas": the whole DPLL list item (lines 416–452)

This is the main content change: the sentence claiming CDCL is "currently not
implemented" is replaced by a pointer to the new solver, the solver ladder
grows from three to four entries, and a new entry describes the cdcl solver.

OLD (the complete block, from the DPLL `<li>` to the end of the inner list):
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

## Edit 5 — "State of the art solvers" section (after line 481)

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

## Edit 6 — "Generating problems" help text, two occurrences (lines 561 and 713)

OLD (occurrence 1, in the main help section):
```html
    <p><p>For DPLL try out 200 variables or
    more. Truth table solvers start running into trouble with more than 20 variables. The resolution
    provers are a bit better than the truth table solvers, yet much worse than the DPLL solvers.</li>
```

NEW:
```html
    <p><p>For cdcl and DPLL try out 200 variables or
    more. Truth table solvers start running into trouble with more than 20 variables. The resolution
    provers are a bit better than the truth table solvers, yet much worse than the cdcl and DPLL solvers.</li>
```

OLD (occurrence 2, in the generateModal dialog — note the different indentation):
```html
          <p><p>For DPLL try out 200 variables or
          more. Truth table solvers start running into trouble with more than 20 variables. The resolution
          provers are a bit better than the truth table solvers, yet much worse than the DPLL solvers.</li>
```

NEW:
```html
          <p><p>For cdcl and DPLL try out 200 variables or
          more. Truth table solvers start running into trouble with more than 20 variables. The resolution
          provers are a bit better than the truth table solvers, yet much worse than the cdcl and DPLL solvers.</li>
```

## Edit 7 — solveModal dialog, best-solver sentence (lines 618–620)

OLD:
```html
        You can select and try out several solver algorithms: 
        the "<a href='http://en.wikipedia.org/wiki/DPLL_algorithm'>DPLL</a> better" 
        is the best solver amongst the options. 
```

NEW:
```html
        You can select and try out several solver algorithms: 
        "<a href='https://en.wikipedia.org/wiki/Conflict-driven_clause_learning'>cdcl</a>: clause learning" 
        is the best solver amongst the options. 
```

## Edit 8 — commented-out script list at the bottom (lines 763–765 area)

Keep `<script src="proplog_min.js"></script>` as the live loader (the bundle is
rebuilt in PLAN Step 4); just add the new file to the commented reference list.

OLD:
```html
<script src="proplog_dpll.js"></script>
<script src="proplog_olddpll.js"></script>
<script src="proplog_naivedpll.js"></script>
```

NEW:
```html
<script src="proplog_cdcl.js"></script>
<script src="proplog_dpll.js"></script>
<script src="proplog_olddpll.js"></script>
<script src="proplog_naivedpll.js"></script>
```
