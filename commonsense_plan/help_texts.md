# Commonsense tab: page help texts

Final text content for the commonsense reasoner page, in the slots used by the
existing `index.html` layout. All fragments are HTML in the site's existing
style. Wording is final unless marked (build note).

---

## 1. Page metadata

- `<title>`: `Logictools: commonsense reasoning`
- meta description: `Online commonsense reasoner: uncertain knowledge, defaults and exceptions, contradictions.`
- meta keywords: `commonsense reasoning, logic, solver, defaults, exceptions, uncertainty, confidence, nonmonotonic`

## 2. Navbar

New item between "Predicate logic" and "Propositional logic":

```html
<li class="dummy"><a href="commonsense.html">Commonsense</a></li>
```

(add the same item to the maintained navbar pages listed in the plan; on
`commonsense.html` it carries `class="active"`).

## 3. Top-of-page intro (above the input area)

<p>
Type your knowledge and a question into the text box, then press <i>solve</i>:
the <a href="https://github.com/tammet/gkreasoner">gk reasoner</a> compiled
into WebAssembly runs in your browser and prints the answer with a proof.
Unlike the classical <a href="index.html">predicate logic solver</a>, gk
handles knowledge that is uncertain, contradictory or true only by default:
statements carry confidences, rules can have exceptions, and evidence against
an answer is weighed against the evidence for it.
</p>
<p>
The first example menu introduces the main features. The second contains
alternative input notations and longer problems. Selecting an example fills
the text box and shows input and result notes.
</p>

## 4. Syntax quick reference (collapsible box, like the predicate page's "syntax")

<h4>Syntax in brief</h4>
<p>Statements end with a period. <code>%</code> starts a line comment,
<code>/* ... */</code> a block comment. Uppercase names are variables,
lowercase names are constants, predicates and functions.</p>
<table class="table table-condensed">
<tr><td><code>bird(b).</code></td>
    <td>a fact</td></tr>
<tr><td><code>-bird(airplane).</code></td>
    <td>a negative fact: evidence against</td></tr>
<tr><td><code>0.8::rain(today).</code></td>
    <td>a fact believed with confidence 0.8</td></tr>
<tr><td><code>flies(X) :- bird(X), healthy(X).</code></td>
    <td>a rule: head <code>:-</code> conditions</td></tr>
<tr><td><code>0.7::rain(X) :- dark_clouds(X).</code></td>
    <td>an uncertain rule</td></tr>
<tr><td><code>flies(X) :- bird(X), unless(-flies(X), 2).</code></td>
    <td>a default rule with priority 2: applies unless
        <code>-flies(X)</code> can be argued</td></tr>
<tr><td><code>male(X) ; female(X) :- person(X).</code></td>
    <td>alternative conclusions (or)</td></tr>
<tr><td><code>:- penguin(X), flies(X).</code></td>
    <td>a constraint: these cannot hold together</td></tr>
<tr><td><code>f(a) = g(b).&nbsp;&nbsp;a != b.</code></td>
    <td>equality and inequality</td></tr>
<tr><td><code>few(P) :- apples(P, N), N &lt; 5.</code></td>
    <td>arithmetic: <code>+ - * /</code> and
        <code>&lt; &gt; =&lt; &gt;=</code></td></tr>
<tr><td><code>query(flies(X)).</code></td>
    <td>the question; a variable asks for a value,
        a ground query for a truth assessment</td></tr>
</table>
<p>This is the GKP notation. The same text box also accepts gk's JSON
notation, the GKS notation and TPTP clause form &mdash; the language is
detected automatically; see examples 16&ndash;18 in the <i>more examples</i>
menu. There is no Prolog-style cut, <code>is</code> or negation as failure:
use explicit negation or <code>unless</code>. Full reference:
<a href="https://github.com/tammet/gkreasoner/blob/master/Doc/input_languages.md">input languages</a>.</p>

## 5. Modal: "what is this?" (linked from the intro, like the predicate page's solveModal)

<h4>What this solver does</h4>
<p>gk is a first-order reasoner built on the
<a href="index.html">gkc</a> theorem prover. It uses resolution proof search
and adds:</p>
<ul>
<li><b>Confidences.</b> Any fact or rule can carry a confidence between 0 and
1. A proof multiplies the confidences it uses; several independent proofs of
the same answer are combined so that shared evidence is not counted twice.</li>
<li><b>Evidence against.</b> The negation of a statement can have its own
support. gk runs a separate search for the evidence against an answer and
reports the net result, together with a four-part split into support,
opposition, conflict and ignorance.</li>
<li><b>Defaults and exceptions.</b> Rules with <code>unless</code> apply only
when their exception cannot be argued. Competing defaults are resolved by
priorities. A certain strict argument defeats a default. Candidate answers
defeated by exceptions are shown as rejected answers with their proofs.</li>
<li><b>Contradiction tolerance.</b> Opposing inputs produce conflict reported
for the affected answers. JSON detail output can name contested premises.</li>
</ul>
<p>The reported confidence is an assessment of the proof evidence, not a
probability calculated from a complete probability model. The algorithms are
described in
<a href="https://github.com/tammet/gkreasoner/blob/master/Doc/how_gk_works.md">how gk works</a>.</p>

## 6. Modal: "reading the output"

<h4>Reading the output</h4>
<p>The first line states the overall result. Common values are
<code>answer found</code>; <code>evidence below limit</code> (a proof was
found below the confidence threshold); <code>no information</code> (neither
side of a ground query was proved); <code>no answers found</code> (an open
query produced no values); and <code>time limit, proof not found</code>.</p>
<p>Each answer block contains:</p>
<ul>
<li><code>answer:</code> a value for the query variable, or
<code>true</code>/<code>false</code> for a ground query;</li>
<li><code>confidence:</code> the net degree of belief, 0 to 1;</li>
<li><code>blockers:</code> for answers produced by default rules, the
exception conditions the answer depends on;</li>
<li><code>proof for</code> and, when relevant, <code>proof against</code>:
numbered derivation steps. <code>in(name)</code> is an input statement,
<code>mp(i, j)</code> a resolution step from earlier steps,
<code>cumul(i, j)</code> a combination of independent proofs,
<code>=</code> an equality step. The number at the end of each step is the
confidence at that step;</li>
<li><code>rejected answer:</code> a candidate defeated by exceptions or
opposing evidence, shown with the proofs of both sides.</li>
</ul>
<p>With the <i>detail report</i> switched on (under Advanced), each answer
also shows <code>support / conflict / ignorance</code> lines splitting the
belief into the part supported only for, only against, claimed by both sides,
and claimed by neither &mdash; the four parts sum to 1 &mdash; plus warning
flags such as <code>CONTESTED</code>. JSON detail output can also include a
list of conflict sources.</p>
<p>JSON input produces JSON output; TPTP input produces TPTP-style output.</p>

## 7. Modal: "confidences" (linked from examples 2-7 region / intro)

<h4>How confidences combine</h4>
<p>Four rules cover most of what the examples show:</p>
<ul>
<li><b>Chaining multiplies.</b> A derivation using statements with
confidences c1, c2, ... supports its conclusion with c1 &middot; c2 &middot;
&hellip; (independence assumption).</li>
<li><b>Independent proofs cumulate.</b> Two proofs of the same answer with
supports s1 and s2 give 1 &minus; (1 &minus; s1)(1 &minus; s2), the noisy-or
rule: the answer fails only if both fail.</li>
<li><b>Shared evidence is not double-counted.</b> gk records which input
statements each proof uses; only the non-shared parts of two proofs
cumulate. Two proofs standing on the same uncertain fact are not treated as
independent confirmation.</li>
<li><b>Opposition nets.</b> Evidence against an answer subtracts from the
evidence for it; the contested part is reported as conflict.</li>
</ul>
<p>The reported numbers assess proof evidence under these rules. gk does not
build a complete probability model of the knowledge base.</p>

## 8. Modal: "defaults" (linked from examples 8-12 region)

<h4>Defaults, exceptions and priorities</h4>
<p><code>unless(condition, priority)</code> in a rule body turns the rule into
a default. gk first derives the conclusion as a candidate carrying the
blocker, then searches for arguments for the blocking condition:</p>
<ul>
<li>no blocking proof found &mdash; the answer stands, and its blockers are
listed;</li>
<li>a confidence-1 strict argument (no <code>unless</code> in its own
support) &mdash; the candidate is defeated and shown as a rejected answer;</li>
<li>an argument from a <i>higher-priority</i> default &mdash; likewise
defeated;</li>
<li>an argument from a <i>lower-priority</i> default &mdash; the argument is
ignored;</li>
<li>an <i>equal-priority</i> argument &mdash; a standoff: gk commits to
neither side (the Nixon diamond example).</li>
<li>uncertain evidence for the exception nets against the answer's confidence
without defeating it outright (the exception example).</li>
</ul>
<p>Priorities are numbers, higher wins. In larger knowledge bases priorities
can also be derived from a taxonomy &mdash; a more specific class defeats a
more general one &mdash; using <code>tax(class)</code> in place of a number;
this needs auxiliary data files and is not enabled on this page.</p>

## 9. Advanced panel: control labels and inline help

Controls (mirroring the predicate page's Advanced area), with tooltips /
short labels:

- `seconds` (number input, default 5): "time limit for the search"
- `detail report` (select off/on, default off): "adds
  support/conflict/ignorance lines and warning flags; JSON output can also
  include conflict sources"
- `print level` (select: minimal / +strategy / +runs / +statistics, values
  10/11/12/15, default 10 &mdash; same values as the predicate page)
- `show derived` (select off/on, default off): "prints clauses as they are
  derived during the search; can produce a lot of output"
- `strategy` (text input, default empty): "a JSON strategy overriding gk's
  automatic choice, e.g.
  `{"strategy":["unit"],"query_preference":0,"arith_instantiation":1}` &mdash;
  see the strategy reference" (link:
  https://github.com/tammet/gkreasoner/blob/master/Doc/strategy_reference.md)
- `max answers` (number input, default empty = gk default): "stop after this
  many answers"
- `confidence limit` (number input 0..1, default empty = gk default): "report
  only answers with confidence at least this high"

(build note: seconds and strategy map to `-seconds N` and
`-strategytext '...'`; detail to `-detail`; print level to `-print N`; show
derived to `-derived`; max answers to `-maxanswers N`; confidence limit to
`-confidence X`.)

## 10. Footer / attribution line (bottom of page)

<p>The reasoner running on this page is
<a href="https://github.com/tammet/gkreasoner">gk</a>, compiled to
WebAssembly. Native binaries for Linux, macOS and Windows are listed on the
<a href="download.html">download page</a>. Examples and documentation are in
the
<a href="https://github.com/tammet/gkreasoner">gkreasoner repository</a>.
gk is built on the <a href="https://github.com/tammet/gkc">gkc</a> prover
core. gk is developed by Tanel Tammet, with database technology contributions
by Priit Järv and conceptual ideas by Tanel Tammet, Priit Järv, and Dirk
Draheim.</p>

## 11. Addition to about.html

One sentence added to the existing solver list paragraph:

<p>The <a href="commonsense.html">commonsense page</a> runs the
<a href="https://github.com/tammet/gkreasoner">gk reasoner</a> in the
browser: predicate logic extended with confidences, defaults with exceptions,
and tolerance of contradictions.</p>

## 12. Addition to download.html

<p>The <a href="commonsense.html">commonsense solver</a> gk can be downloaded
from the <a href="https://github.com/tammet/gkreasoner">gkreasoner
repository</a>: Linux, macOS, Windows and WebAssembly files are in
<code>bin/</code>, with examples and documentation alongside.</p>
