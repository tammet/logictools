# Plan for the sol_notes.txt review of commonsense.html

Assessment of each point of `sol_notes.txt` (the 2026-07-22 review of the
Reasoning under uncertainty page), with a verdict per point and the order of
work. Claims marked "verified" were reproduced before deciding: the example 12
deletion variants were both run (deleting both lines gives `no answers found`,
deleting only the move line gives hallway 0.9801), and the example 5 and 23
calculations were recomputed.

## Batch A -- done in one pass (page-side text, CSS, small JS)

| Sol's point | Verdict |
|---|---|
| Ex12 deletion instruction wrong | Fixed; verified. Delete only `move(john, kitchen, s2, s3).`, keep `next(s2, s3).` |
| Ex23 calculation omits the human 0.3 | Fixed; verified: 1-(1-0.936)(1-0.3)=0.9552, minus 0.4 = 0.5552. The old text's numbers only gave 0.536. |
| Ex5 explanation does not reach 0.3764 | Arithmetic spelled out, including the 0.1 friends fact: pooled friendship 0.91, chain 0.91*0.6*0.2=0.1092, noisy-or with 0.3 = 0.3764. The suggested reordering of examples 5/6 is NOT done (renumbering churn across harnesses, notes and modal references; the expanded note achieves the goal). |
| Ex18 "source list" terminology | Fixed to the useful-info annotation list; added that answer extraction from an open variable is a GK convention layered on TPTP CNF. |
| Decode the ex20 plan | Added the four decoded steps. |
| Ex22's actual result unstated | Added the explicit `$some_fox` sentence. |
| Ex21 entity identifier unexplained | Added a sentence on the generated identifier. |
| Ex1 priority omitted vs later numbered defaults | Added: the priority is optional; an unnumbered default is incomparable with numbered ones. |
| Confidence-limit field unclear | Added: it is the minimum net support margin. |
| Search incompleteness unstated | Added to the reading-the-output help: failure to find a proof is not proof of falsity. |
| Ex15 "both directions", ex13 "hold all 42 books", mp() described as binary, four-part phrasing, 0.45 vs 0.46, "neither number is a mistake" | All reworded as suggested (the last one softened: this repo's own history shows a difference CAN indicate a mistake). |
| Help text "the proofs of both sides" | Qualified now (a proof against appears when the explicit negation was derived); the real fix is in Batch C. |
| Dropdown clipping, missing aria-labels, input-area expansion | Dropdown widened, aria-labels added to the advanced fields and sampling selectors, the input box made vertically resizable (the cheap form of the fullscreen control). |
| Ex23 duplicate answer blocks | Interim note now (an answer may be reported through several proof families, each headed by the same aggregate confidence); the renderer change is in Batch C. |

## Batch B -- medium effort, worth doing, needs a wording/design decision first

- Answer summary first with collapsible proofs (sol's top structural item).
  Page-side: wrap the `proof for:` / `proof against:` blocks of the prolog
  text output in collapsible sections; apply only when the output matches
  that shape, leaving the JSON and TPTP examples as they are.
- Relabeling "rejected answer / confidence against: 0" as blocked candidate /
  rejected by opposing evidence / undecided standoff. Real problem, and
  computable from fields the renderer already has -- but it is a gk OUTPUT
  change: restrict to the prolog text renderer, keep the JSON envelope
  untouched (llmpipe reads `rejected_answers`), and re-pin the page harness,
  gk fixtures and doc examples. Needs the wording decided first.
- Notes under the empty result box: sol wants them hidden or labelled; the
  page owner explicitly wants them visible from the start. Proposed
  reconciliation: keep them, add a small "Expected result" heading.
- A 2x2 outcome table in the four-masses modal bullet (adapted to threshold
  language: evidence clearing its bar, not "derivable").
- Sampling modal restructure: concept first, mechanics in a collapsible
  technical section.

## Batch C -- hard, later

- Show the blocking proof: the reasoner does not record the subsidiary
  check's derivation in the report; capturing it is a gk feature.
- Group duplicate answer blocks in gk's report: a report-format change with
  downstream consumers and fixtures; belongs in one designed pass together
  with the relabeling above.
- The help button as an in-place panel or modal: structural page rework.

## Not to do

- Renaming "four masses" to "belief-mass check": the term is used
  consistently across the page, the modal that defines it, and the
  gkreasoner montecarlo documentation; renaming the control alone would
  create a fresh inconsistency.
- Reordering examples 5 and 6: see Batch A -- the expanded example 5 note
  achieves the goal without renumbering.
