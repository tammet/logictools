# Commonsense tab: examples

Selected examples, menu names, input texts, and note texts for the commonsense
reasoner page. Embed the input and HTML fragments in the page's hidden example
divs (`example_N_input_notes` / `example_N_proof_notes`). The `Expected
output` blocks are not page content; they are
verification targets for the build phase (all recorded by running the current
`gkreasoner/bin/gk` on 2026-07-20).

Sources are files under `/opt/gkreasoner/Examples/`; several inputs are
adaptations (marked), not verbatim copies.

Per-example UI presets: when an example is selected, the page should also set
the listed Advanced controls (detail on/off, strategy text). Unlisted controls
keep their defaults.

---

## Group 1: dropdown "examples"

### 1. facts and rules

Menu name: `facts and rules`
Source: introductory bird/penguin rule chain.
Presets: none.

Input:

```prolog
penguin(polly).

bird(X) :- penguin(X).
animal(X) :- bird(X).

query(animal(X)).

% Which animal can be derived from these facts and rules?
```

Input notes (HTML):

<h3>Example 1: facts and rules</h3>
<p>Each statement ends with a period. Lowercase names such as
<code>polly</code> are constants, predicates, or functions; uppercase names
such as <code>X</code> are variables. The first rule says that every penguin is
a bird, and the second that every bird is an animal.</p>
<p>The <code>query</code> statement asks the question. Since it contains the
variable <code>X</code>, gk returns each value for which
<code>animal(X)</code> can be derived.</p>
<p>A percent sign <code>%</code> starts a line comment; <code>/* ... */</code>
comments work as well. The order of statements does not matter.</p>

Proof notes (HTML):

<p>The answer is <code>polly</code> with confidence 1. The proof applies the two
rules to the input fact.</p>
<p>The <code>proof for</code> block lists numbered derivation steps.
<code>in(frm_1)</code> marks an input statement;
<code>mp(1, 2)</code> means the step was derived from steps 1 and 2 by
<a href="https://en.wikipedia.org/wiki/Resolution_(logic)">resolution</a>.
The number after each step name is the confidence of that step.</p>
<p>The internal literal <code>$ans(X)</code> collects the answer value: the last
step contains <code>$ans(polly)</code>.</p>

Expected output:

```text
result: answer found
answer: polly
confidence: 1
```

### 2. confidences

Menu name: `confidences`
Source: uncertain weather example.
Presets: none.

Input:

```prolog
0.8::dark_clouds(today).
0.7::rain(X) :- dark_clouds(X).

query(rain(today)).

% There is uncertain evidence for dark clouds and an uncertain
% rule connecting dark clouds with rain.
```

Input notes (HTML):

<h3>Example 2: confidences</h3>
<p>A number between 0 and 1 before <code>::</code> states how strongly the
statement is believed. A statement without the prefix has confidence 1.</p>
<p>Both the facts and the rule can be uncertain. gk computes the confidence of
the answer from the confidences of everything used in the proof.</p>

Proof notes (HTML):

<p>The answer is <code>true</code> with confidence
<code>0.56 = 0.8 * 0.7</code>. A proof chain multiplies the confidences of
the statements it uses, under the assumption that their uncertainties are
independent.</p>

Expected output:

```text
answer: true
confidence: 0.56
```

### 3. several sources

Menu name: `several sources`
Source: adapted from `confidences/cumulate.gkp`.
Presets: none.

Input:

```prolog
0.5::rain(today).
0.6::rain(today).

query(rain(today)).

% Two independent forecasts both predict rain today,
% one with confidence 0.5 and the other with 0.6.
% What is the combined confidence?
```

Input notes (HTML):

<h3>Example 3: several sources</h3>
<p>Two independent sources support the same forecast with different
confidences. Their combined support is greater than either source alone.</p>

Proof notes (HTML):

<p>The combined confidence is <code>0.8</code>. For independent evidence gk
combines the two proofs as
<code>1 - (1 - 0.5) * (1 - 0.6) = 0.8</code>: the answer fails only if both
sources fail. This is the same "noisy-or" rule used in probabilistic logic
programming.</p>
<p>The proof shows both derivations and a <code>cumul</code> step which merges
them. Importantly, gk records which input facts each proof uses and merges this
way only proofs based on different evidence: see the "shared evidence" example.</p>

Expected output:

```text
answer: true
confidence: 0.8
... 6. cumul(3, 5) 0.8: false
```

### 4. for and against

Menu name: `for and against`
Source: `confidences/net_direct.gkp`.
Presets: detail on.

Input:

```prolog
0.7::flies(a).
0.4::-flies(a).

query(flies(a)).

% Evidence for and against the same statement:
% 70% belief that a flies, 40% belief that it does not.
```

Input notes (HTML):

<h3>Example 4: for and against</h3>
<p>The minus sign is explicit negation: <code>-flies(a)</code> is evidence that
<code>a</code> does not fly, not an absence of evidence. Here both the
statement and its negation have direct support. gk retains and assesses both
sides.</p>
<p>The <i>detail report</i> option (in Advanced) is switched on for this
example: it adds a breakdown of the evidence to the answer.</p>

Proof notes (HTML):

<p>The answer <code>true</code> has confidence <code>0.3</code>: the positive
evidence 0.7 minus the part 0.4 contested by the negative evidence.</p>
<p>The detail lines split the total belief into four parts which sum to 1:</p>
<pre><code>support: 0.3 for, 0 against
conflict: 0.4   ignorance: 0.3</code></pre>
<p><i>Support</i> is the uncontested evidence on each side. <i>Conflict</i> is
the part claimed by both sides at once. <i>Ignorance</i> is the part supported
by neither side. The <code>CONTESTED</code> flag warns that the answer has
real evidence against it, not merely weak evidence for it.</p>
<p>Both the <code>proof for</code> and the <code>proof against</code> are
printed, so you can see exactly what supports each side.</p>

Expected output:

```text
answer: true
confidence: 0.3
support: 0.3 for, 0 against
conflict: 0.4   ignorance: 0.3
flags: CONTESTED
```

### 5. rule chains

Menu name: `rule chains`
Source: `confidences/smokes.gkp`.
Presets: none.

Input:

```prolog
% Social smoking, following a classical example from
% probabilistic logic programming.

0.3::smokes(X).
0.1::friends(X, Y).
0.9::friends(Y, X) :- friends(X, Y).
0.6::susceptible(X).
0.2::smokes(X) :- susceptible(X), friends(X, Y), smokes(Y).

friends(chris, sam).
smokes(chris).

query(smokes(sam)).
```

Input notes (HTML):

<h3>Example 5: rule chains</h3>
<p>Uncertain rules with variables act as weak general tendencies: anybody
smokes with confidence 0.3, any two people are friends with confidence 0.1,
friendship is roughly symmetric, and a susceptible person with a smoking
friend has an extra 0.2 tendency to smoke. On top of these there are two
certain facts about <code>chris</code> and <code>sam</code>.</p>
<p>The question is how strongly the rules and facts together support
<code>smokes(sam)</code>.</p>

Proof notes (HTML):

<p>The confidence is <code>0.3764</code>. Several different derivations
support the answer: the base tendency (0.3), and a chain through the certain
facts &mdash; sam is a friend of chris (via symmetry, 0.9), chris smokes, sam
may be susceptible (0.6) &mdash; contributing on top of the base rate. gk finds
the separate proofs and cumulates them, multiplying confidences along each
chain and combining the chains with the noisy-or rule.</p>
<p>The <code>cumul</code> steps in the proof show where the independent
derivations are merged.</p>

Expected output:

```text
answer: true
confidence: 0.3764
```

### 6. shared evidence

Menu name: `shared evidence`
Source: adapted to GKP from `confidences/overlap1.js` (same logic, verified
equal result).
Presets: none.

Input:

```prolog
0.9::fa(x).
0.8::fb(x).
0.7::fc(x).

g(X) :- fa(X), fb(X).
g(X) :- fa(X), fc(X).

query(g(x)).

% Two different rules derive g(x), but both depend
% on the same uncertain fact fa(x).
```

Input notes (HTML):

<h3>Example 6: shared evidence</h3>
<p>Two proofs support <code>g(x)</code>: one through <code>fa</code> and
<code>fb</code> (confidence 0.72), another through <code>fa</code> and
<code>fc</code> (confidence 0.63). Combining them naively with the noisy-or
rule would give <code>1 - 0.28 * 0.37 = 0.896</code>.</p>
<p>But that would be wrong: both proofs stand on the <i>same</i> uncertain
fact <code>fa(x)</code>. If <code>fa(x)</code> fails, both proofs fail
together, so the two proofs are not independent.</p>

Proof notes (HTML):

<p>gk returns <code>0.846</code>, not 0.896. It records which input facts each
proof uses, notices that <code>fa(x)</code> is shared, and combines only the
non-shared parts independently:
<code>0.9 * (1 - (1 - 0.8) * (1 - 0.7)) = 0.9 * 0.94 = 0.846</code>.</p>
<p>Replacing <code>fa(X)</code> in the second rule with an independent
<code>fd(X)</code> of confidence 0.9 removes the overlap and changes the result
to 0.8964.</p>

Expected output:

```text
answer: true
confidence: 0.846
```

### 7. contested premises

Menu name: `contested premises`
Source: adapted to GKP from `confidences/net_premise.js`.
Presets: detail on.

Input:

```prolog
0.5::bird(a).
0.2::-bird(a).

0.9::flies(X) :- bird(X).

query(flies(a)).

% The premise bird(a) is itself contested:
% how does that affect the derived conclusion?
```

Input notes (HTML):

<h3>Example 7: contested premises</h3>
<p>Here the conflict is not about the queried statement itself but about a
premise used to derive it: <code>bird(a)</code> has evidence both for (0.5)
and against (0.2).</p>
<p>The detail report is switched on to show how gk flags this.</p>

Proof notes (HTML):

<p>The conclusion gets confidence <code>0.27</code>: the flying rule (0.9)
applied to the net support of its premise. The
<code>flags: CONTESTED</code> line marks that a premise of the proof has
opposing evidence.</p>
<p>JSON detail output can also list contested atoms as
<code>conflict_sources</code>; see the "conflict detail" example under
<i>more examples</i>.</p>

Expected output:

```text
answer: true
confidence: 0.27
support: 0.27 for, 0 against
conflict: 0   ignorance: 0.73
flags: CONTESTED
```

### 8. defaults

Menu name: `defaults`
Source: `exceptions/bird_default.gkp`.
Presets: none.

Input:

```prolog
bird(a).
bird(b).

flies(X) :- bird(X), unless(-flies(X), 2).

query(flies(X)).

% Birds fly by default: the rule applies unless
% it can be shown that the bird does not fly.
```

Input notes (HTML):

<h3>Example 8: defaults</h3>
<p>The <code>unless(-flies(X), 2)</code> condition makes this a <i>default
rule</i>: derive <code>flies(X)</code> from <code>bird(X)</code> unless an
argument for <code>-flies(X)</code> blocks it. The number 2 is the priority of
the default, used when defaults compete; see the later examples.</p>
<p>This states that birds normally fly without claiming that every bird
flies.</p>

Proof notes (HTML):

<p>Both <code>a</code> and <code>b</code> are answers with confidence 1: there
is no evidence against either of them flying, so the defaults go through.</p>
<p>Each answer records its <code>blockers</code> &mdash; the exception
condition it depends on, e.g. <code>unless(-flies(b), 2)</code>. The answer is
conditional on no such blocker being derivable: gk searched for evidence of
the exceptions and found none.</p>
<p>Try adding the fact <code>-flies(a).</code> and solving again:
<code>a</code> disappears from the answers, <code>b</code> remains.</p>

Expected output:

```text
answer: b
confidence: 1
blockers: unless(-flies(b), 2)
answer: a
confidence: 1
```

### 9. an exception

Menu name: `an exception`
Source: `exceptions/bird_exception.gkp`.
Presets: none.

Input:

```prolog
bird(a).
bird(b).
0.9::-flies(a).

flies(X) :- bird(X), unless(-flies(X), 2).

query(flies(X)).

% As before, but now there is 90%-confidence evidence
% that a does not fly.
```

Input notes (HTML):

<h3>Example 9: an exception</h3>
<p>The new fact <code>0.9::-flies(a)</code> is evidence for the exception of
the default, but it is uncertain: 0.9 rather than 1.</p>

Proof notes (HTML):

<p><code>b</code> still flies with confidence 1. For <code>a</code> the
uncertain exception does not eliminate the default outright; it nets against
it: the answer <code>a</code> remains with confidence
<code>1 - 0.9 = 0.1</code>.</p>
<p>The output shows both the <code>proof for</code> (the default) and the
<code>proof against</code> (the exception evidence) for <code>a</code>.</p>
<p>Try changing <code>0.9</code> to <code>1</code>: with a certain exception
the answer <code>a</code> is fully defeated.</p>

Expected output:

```text
answer: b
confidence: 1
answer: a
confidence: 0.1
```

### 10. penguins

Menu name: `penguins`
Source: adapted from `exceptions/penguin.gkp`.
Presets: none.

Input:

```prolog
bird(b).
penguin(p).

bird(X)   :- penguin(X).
object(X) :- bird(X).
-flies(X) :- penguin(X).

flies(X)  :- bird(X),   unless(-flies(X), 3).
-flies(X) :- object(X), unless(flies(X), 2).

query(flies(X)).

% Birds fly, penguins are birds, penguins
% do not fly. Also: objects in general do not fly.
```

Input notes (HTML):

<h3>Example 10: penguins</h3>
<p>Two default rules compete: birds fly (priority 3) and objects do not fly
(priority 2). Since every bird is an object, both defaults apply to every
bird. The higher priority number wins, so for ordinary birds the flying
default defeats the non-flying one.</p>
<p>The penguin rule <code>-flies(X) :- penguin(X)</code> has no
<code>unless</code>: it is strict, and strict conclusions override any
default.</p>

Proof notes (HTML):

<p>The bird <code>b</code> flies with confidence 1: its priority-3 default
defeats the priority-2 object default (the printed <code>proof against</code>
shows the defeated attempt).</p>
<p>The penguin <code>p</code> is printed as a <i>rejected answer</i> with
confidence against 1: the flying default produced a candidate, but the strict
penguin rule defeats it regardless of priorities.</p>
<p>The rejected-answer block records the defeated candidate and its opposing
proof.</p>

Expected output:

```text
answer: b
confidence: 1
rejected answer: p
confidence against: 1
```

### 11. Nixon diamond

Menu name: `Nixon diamond`
Source: `exceptions/nixon.gkp`.
Presets: detail on.

Input:

```prolog
quaker(n).
republican(n).

pacifist(X)  :- quaker(X),     unless(-pacifist(X), 2).
-pacifist(X) :- republican(X), unless(pacifist(X), 2).

dislikeswar(X) :- pacifist(X).

query(dislikeswar(X)).

% Quakers are pacifists; republicans are not.
% Nixon is both. Does he dislike war?
```

Input notes (HTML):

<h3>Example 11: the Nixon diamond</h3>
<p>Two defaults of <i>equal</i> priority support opposite conclusions about
the same person: the quaker rule supports pacifism and the republican rule
supports its negation.</p>
<p>The query asks about a further consequence of pacifism.</p>

Proof notes (HTML):

<p>gk reports <code>result: evidence below limit</code> and shows
<code>n</code> only as a rejected answer with confidence against 0 and the
<code>CONTESTED</code> flag. Neither default can defeat the other &mdash; the
priorities are equal &mdash; so the margin between them is zero: gk commits
to neither <code>pacifist(n)</code> nor its negation, and the downstream
conclusion is left undecided (ignorance 1 in the detail lines).</p>
<p>Try raising the quaker default to priority 3: then pacifism wins and
<code>n</code> becomes a real answer with confidence 1.</p>

Expected output:

```text
result: evidence below limit
rejected answer: n
confidence against: 0
flags: CONTESTED
```

### 12. a story

Menu name: `a story`
Source: `exceptions/people_room.js` (verbatim).
Presets: none.

Input: the full text of `Examples/exceptions/people_room.js` including its
comment header (the comments explain the encoding; keep them).

Input notes (HTML):

<h3>Example 12: a story about situations</h3>
<p>The story: <i>"A man entered a room containing a table. He wore a black
suit. Then the man left the room."</i> The question: in which situations is
the man in the room?</p>
<p>This example is written in gk's native JSON syntax (see the notation
examples under <i>more examples</i>) and shows a typical commonsense encoding
of time: situations <code>sit1, sit2, sit3</code> connected by events, with
<i>frame rules</i> stating that facts persist from one situation to the next
by default &mdash; unless an event changes them.</p>

Proof notes (HTML):

<p>Because the input is in JSON syntax, the output is JSON as well. The man is
in the room in <code>sit2</code> (after entering): a real answer with
confidence 1.</p>
<p><code>sit3</code> (after leaving) appears among the rejected answers: the
persistence default suggested he might still be in the room, but the leave
event defeats it. <code>sit1</code> is rejected as well, in the other
direction: persistence backwards from <code>sit2</code> is defeated since
the enter event is exactly what put him there.</p>
<p>This defeat of persistence by known events is the classical
<a href="https://en.wikipedia.org/wiki/Frame_problem">frame problem</a>
handled with defaults.</p>

Expected output:

```text
"answer": [["$ans","sit2"]], confidence 1.0000
rejected: sit3 (blocked persistence), sit1 (confidence 0)
```

---

## Group 2: dropdown "more examples"

### 13. arithmetic

Menu name: `arithmetic`
Source: `arithmetic/apples_answer.gkp`.
Presets: strategy field prefilled with
`{"strategy":["unit"],"query_preference":0,"arith_instantiation":1}`.

Input:

```prolog
0.8::johnhad(X) :- X + 2 = 10.

query(johnhad(X)).

% John had some apples. Receiving 2 more made 10.
% How many did he have before? Note the strategy field
% under Advanced: it shows the arithmetic setting used
% to find a numeric value for X.
```

Input notes (HTML):

<h3>Example 13: arithmetic</h3>
<p>Ground arithmetic (<code>3 + 4 &lt; 10</code> etc) is evaluated during
proof search. To find a value for a variable in an arithmetic condition, gk
uses bounded enumeration of candidate values. Automatic selection enables
this when required; the preset strategy shows the corresponding
<code>arith_instantiation</code> setting.</p>

Proof notes (HTML):

<p>The answer is <code>8</code> with confidence 0.8 (the rule's own
confidence). The proof shows the instantiation step where <code>X = 8</code>
makes <code>8 + 2 = 10</code> true.</p>
<p>This is bounded search for satisfying values, not equation solving: it
handles one unknown conservatively (<code>arith_instantiation: 1</code>), and
mode 2 also tries selected two-variable cases.</p>

Expected output:

```text
answer: 8
confidence: 0.8
```

### 14. equality

Menu name: `equality`
Source: `core/algebra.js` (verbatim).
Presets: none.

Input: the full text of `Examples/core/algebra.js`.

Input notes (HTML):

<h3>Example 14: equality reasoning</h3>
<p>Group-theory style axioms in JSON notation: an inverse
(<code>m(X, i(X)) = e</code>), a right identity and associativity. The
question asks whether <code>m(e, c) = c</code> follows &mdash; note that only
the <i>right</i> identity is given, so the left identity has to be derived.</p>
<p>gk handles equality with dedicated inference rules (paramodulation), the
same machinery used by classical theorem provers.</p>

Proof notes (HTML):

<p>The answer is <code>true</code> with confidence 1. The <code>=</code> steps
in the proof are equality replacements: the derivation rewrites
<code>m(e, c)</code> using the axioms until it reduces to <code>c</code>.</p>

Expected output:

```text
"answer": true, "confidence": 1.0000
```

### 15. conflict detail

Menu name: `conflict detail`
Source: `core/negation_conflict.js` (verbatim).
Presets: detail on.

Input: the full text of `Examples/core/negation_conflict.js`.

Input notes (HTML):

<h3>Example 15: conflict sources in detail</h3>
<p>Several sources give evidence about whether <code>a</code> is a bird
&mdash; two for, one against &mdash; and rules derive flying from birdness in
both directions. The detail report (switched on for this example) names which
atom the conflict comes from.</p>

Proof notes (HTML):

<p>The answer has confidence <code>0.252</code> and its detail block lists</p>
<pre><code>"conflict_sources": [{"atom": ["bird","a"], "conflict": 0.7000}]</code></pre>
<p>naming the contested premise and the size of the conflict on it: the two
positive sources for <code>bird(a)</code> cumulate to 0.98, the negative
source claims 0.7 of that mass. The <code>CONTESTED</code> flag and the
conflict-source list identify the affected premise.</p>

Expected output:

```text
"confidence": 0.2520
"conflict_sources": [{"atom": ["bird","a"], "conflict": 0.7000}]
"flags": ["CONTESTED"]
```

### 16. JSON notation

Menu name: `JSON notation`
Source: JSON-LD-LOGIC form of example 2.
Presets: none.

Input:

```json
[
  {"@logic": ["dark_clouds", "today"], "@confidence": 0.8},
  {"@logic": [["-dark_clouds", "?:X"], ["rain", "?:X"]],
   "@confidence": 0.7},
  {"@question": ["rain", "today"]}
]
```

Input notes (HTML):

<h3>Example 16: JSON notation</h3>
<p>The weather example is written in gk's
<a href="https://github.com/tammet/json-ld-logic">JSON-LD-LOGIC</a> notation.
The input is a JSON list, variables start with <code>?:</code>, and keys such
as <code>@confidence</code> and <code>@question</code> attach metadata.</p>
<p>This notation is intended for logic generated or consumed by programs.</p>

Proof notes (HTML):

<p>When the input is JSON, the output is JSON as well: machine-readable
answers with the same proofs as in the text format. Confidence 0.56 matches
example 2 because the two inputs encode the same statements.</p>

Expected output:

```text
"answer": true, "confidence": 0.5600
```

### 17. GKS notation

Menu name: `GKS notation`
Source: GKS form of example 2.
Presets: none.

Input:

```text
% Weather example in premise-to-consequence GKS notation.

0.8 :: dark_clouds(today).
0.7 :: dark_clouds(X) => rain(X).

query(rain(today)).
```

Input notes (HTML):

<h3>Example 17: GKS notation</h3>
<p>The third input notation: rules are written premises-first with
<code>&amp;</code> and <code>=&gt;</code>, closer to textbook logic than the
Prolog-style <code>:-</code> form. Everything else &mdash; confidences,
queries, <code>unless</code> &mdash; is the same.</p>
<p>gk detects the notation automatically from the input text, so all the
notations work in this same text box.</p>

Proof notes (HTML):

<p>The answer is true with confidence 0.56, as in examples 2 and 16. All
three inputs are translated to the same internal logic before proof search.</p>

Expected output:

```text
answer: true
confidence: 0.56
```

### 18. TPTP notation

Menu name: `TPTP notation`
Source: `exceptions/bird_penguin.p` (verbatim).
Presets: none.

Input: the full text of `Examples/exceptions/bird_penguin.p`.

Input notes (HTML):

<h3>Example 18: TPTP notation</h3>
<p>gk also reads clause-normal-form problems in the
<a href="https://tptp.org">TPTP</a> notation used by automated theorem
provers, extended with a <code>confidence(...)</code> annotation in the source
list. This example asks which object does not fly.</p>

Proof notes (HTML):

<p>With TPTP input the answer comes back in the TPTP style: an
<code>SZS status</code> line and the proof as an inference list. The penguin
is reported with confidence against 0.08 below the default reporting limit,
hence <code>GaveUp</code> with the rejected-answer support shown.</p>
<p>The output notation follows the input notation.</p>

Expected output:

```text
% SZS status GaveUp
% gk rejected answer: p, confidence against: 0.08
```

### 19. defaults in JSON

Menu name: `defaults in JSON`
Source: `exceptions/gbirds.js` (verbatim).
Presets: none.

Input: the full text of `Examples/exceptions/gbirds.js`.

Input notes (HTML):

<h3>Example 19: defaults in JSON</h3>
<p>The birds-and-penguins default in JSON notation. What GKP writes as
<code>unless(-flies(X), 3)</code> appears here as an explicit
<code>$block</code> literal inside the rule clause:
<code>["$block", 3, ["$not", ["flies", "?:X"]]]</code>. The GKP and GKS
<code>unless</code> forms are translated to exactly this.</p>

Proof notes (HTML):

<p><code>b1</code> flies (confidence 1); the answer lists its
<code>$block</code> blocker just as the text format lists
<code>blockers:</code>. Programs generating JSON-LD-LOGIC use this form
directly.</p>

Expected output:

```text
"answer": true, "confidence": 1.0000
"blockers": [["$block",3,["$not",["flies","b1"]]]]
```

### 20. planning (slow)

Menu name: `planning (slow)`
Source: `fol_comparison/blocks.gkp` (verbatim).
Presets: seconds set to 30.

Input: the full text of `Examples/fol_comparison/blocks.gkp`.

Input notes (HTML):

<h3>Example 20: blocks-world planning</h3>
<p>A classical planning problem: blocks on a table, a robot arm, and a goal
configuration. The plan is found as the answer term: a nested sequence of
<code>pickup</code>/<code>putdown</code> actions transforming the initial
situation.</p>
<p>The time limit is preset to 30 seconds. The search runs on the page's main
thread until it finishes.</p>

Proof notes (HTML):

<p>The answer is a situation term: read it inside-out, starting from
<code>s0</code>, as the sequence of actions of the plan. Unbound variables in
the term (like <code>X3</code>) mark actions whose details do not matter for
reaching the goal.</p>

Expected output:

```text
answer: do(putdown(c,b),do(pickup(c),do(putdown(b,a),do(pickup(b),s0))))
confidence: 1
```

### 21. English: penguins

Menu name: `English: penguins`
Source: `language/penguin_default.js` (verbatim), with
`language/axioms_std.js` loaded as a background knowledge base.
Presets: strategy field prefilled with
`{"strategy": ["negative_pref", "posunitpara"], "query_preference": 1}`;
confidence threshold 0.1 (i.e. the extra arguments
`-confidence 0.1`).

Input: the full text of `Examples/language/penguin_default.js` including its
comment header.

Input notes (HTML):

<h3>Example 21: logic generated from English</h3>
<p>The input was machine-generated by the
<a href="https://github.com/tammet/nlpsolver/tree/main/llmpipe">llmpipe</a>
pipeline, which uses a large language model to translate English to gk logic:
the story is <i>"Penguins are birds. Penguins cannot fly. Birds can fly. John
is a penguin. John flies?"</i>. Each clause carries its source sentence in the
<code>@nl</code> field.</p>
<p>The encoding uses events with actors and types rather than a simple
<code>flies(john)</code> atom, so that the same scheme covers arbitrary verbs,
and a shared background knowledge base (loaded automatically for this
example, not visible in the text box) supplies general axioms for taxonomy,
part-whole relations, degrees, events and space.</p>

Proof notes (HTML):

<p>The expected answer is <code>false</code>: John, a penguin, does not fly.
The "birds can fly" sentence became a default (note the <code>$block</code>
in its clause and its 0.9 confidence) which the strict penguin sentence
defeats, exactly the penguin pattern from the earlier examples &mdash; only
now produced automatically from English text.</p>

Expected output:

```text
"answer": false (the negated question is derived)
```

### 22. English: which cannot fly

Menu name: `English: which one`
Source: `language/which_cannot_fly.js` (verbatim), with `axioms_std.js`
pre-loaded as in example 21.
Presets: as in example 21.

Input: the full text of `Examples/language/which_cannot_fly.js` including its
comment header.

Input notes (HTML):

<h3>Example 22: a which-question from English</h3>
<p>A wh-question produced by the same English-to-logic pipeline. The answer
value comes back wrapped in <code>$ans</code>: a name like
<code>#:John 1</code> is a specific individual mentioned in the text, while a
value like <code>$some_fox</code> is an existential one &mdash; "a fox",
introduced by the text without a name.</p>

Proof notes (HTML):

<p>The answer here is such an existential individual. Population clauses
(marked <code>@sourcetype: "populate"</code>) supply typical members for the
classes mentioned in the text, so that questions about "a fox" or "some bird"
have witnesses to find.</p>

Expected output:

```text
"answer": [["$ans","$some_fox"]], confidence 1.0000
```

---

## 23. taxonomy classification (implemented 2026-07-21)

Menu name: `taxonomy classification` (in "more examples").
Source: `exceptions/classify.gkp` (comment header shortened) with `-defaults`.
Presets: `taxonomy: true` — the page fetches `gk_name_number.txt.gz`
(0.65 MB) and `gk_taxonomy_packed.txt.gz` (0.26 MB), decompresses them with
`DecompressionStream("gzip")`, hands them to the solver worker's in-memory
filesystem, and adds `-defaults` to the arguments. The final note texts are
in the page's `example_cs23_*` divs.

This example needed a gk fix first: under wasm (and win32) the `-mbsize`
option was silently inert and the database defaulted to the 10 MB
`DEFAULT_MEMDBASE_SIZE` fallback instead of the intended 100 MB, so the
taxonomy load ran out of datarec space. Fixed in `Main/gk.c` (gk 1.0.1,
2026-07-20): the `} else {` of the size-default block sat inside the
non-windows preprocessor branch. With the fix the example runs at the wasm
default size; no `-mbsize` needed.

Expected output: answer `b1` confidence 0.5552 (twice, via the human- and
bird-default routes, blockers `unless(-isa(b1,human), tax(human))` /
`unless(-isa(b1,bird), tax(bird))`), answer `h1` confidence 0.44 (twice),
rejected answer `a1` with confidence against 1 (strict engine rule).
