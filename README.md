# logictools

We help to study logic solvers by providing and collecting various 
easy-to-use, browser-based javascript tools: starting with classical propositional formulas 
and continuing with predicate logic later. 

All the code is self-contained, no-dependencies, easy-to-hack javascript under the
<a href="https://en.wikipedia.org/wiki/MIT_License">MIT licence</a>.

The focus is on simplicity, ease of use, hacking and experimenting, 
not state of the art efficiency-wise.

Help and cooperation appreciated for improving the current code, writing and proposing new tools, etc. 
See <a href="http://logictools.org">the site with functioning code</a>.

Site,  initial solvers and utilities written by Tanel Tammet (tanel.tammet at gmail.com) 

<b>User interface</b> for trying out all the functions:

<ul>
<li><a href="proplog.html">proplog.html</a> a barebones webpage without menus, design, bootstrap or jquery</li>
<li><a href="proplog_ui.js">proplog_ui.js</a> calling the algorithms below </li>
</ul>

<b>Solvers</b> for experimenting with different algorithms are self-contained:

<ul>
<li><a href="proplog_dpll.js">proplog_dpll.js</a> the best solver among the ones provided</li>
<li><a href="proplog_olddpll.js">proplog_olddpll.js</a> old-style dpll: no learning and full pure literal elimination</li>
<li><a href="proplog_naivedpll.js">proplog_naivedpll.js</a> naive minimal dpll, easy to understand</li>
<li><a href="proplog_res.js">proplog_res.js</a> optimized resolution method: better than table search, worse than dpll</li>
<li><a href="proplog_naiveres.js">proplog_naiveres.js</a> naive minimal resolution, easy to understand</li>
<li><a href="proplog_searchtable.js">proplog_searchtable.js</a> basic table search: both leaves-only and all-nodes test options </li>
</ul>

<b>Utilities</b> are also self-contained:

<ul>
<li><a href="proplog_parse.js">proplog_parse.js</a> parse formula and dimacs syntaxes</li>
<li><a href="proplog_convert.js">proplog_convert.js</a> 
  convert to cnf, rename variables, print formulas, build and print the full truth table</li>
<li><a href="proplog_generate.js">proplog_generate.js</a> problem generators </li>
</ul>
