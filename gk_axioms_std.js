[
  // == 1. BASIC TAXONOMY ==
  [["-isa", "thing", "?:Y"], ["isa", "object", "?:Y"]],
  [["-isa", "object", "?:Y"], ["isa", "thing", "?:Y"]],

  // == 2. PART-WHOLE & POSSESSION  ==
  // If Y1 is a subtype of Y2, and Y1 has part X, then Y2 has part X
  [
    ["-isa", "?:Y1", "?:Y2"], 
    ["-has part", "?:Y1", "?:X", "?:Ctxt"], 
    ["has part", "?:Y2", "?:X", "?:Ctxt"]
  ],
  // "Has part" implies "Have" (possession) [cite: 127, 345]
  [
    ["-has part", "?:Y", "?:X", "?:Ctxt"], 
    ["have", "?:Y", "?:X", "?:Ctxt"]
  ],
  // Transitivity of Part-Whole
  [
    ["-has part", "?:A", "?:B", "?:Ctxt"],
    ["-has part", "?:B", "?:C", "?:Ctxt"],
    ["has part", "?:A", "?:C", "?:Ctxt"]
  ],
  
  /*
  // == X. INSIDE, OUTSIDE etc  ==
  [ 
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"], 
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"],  
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"]
  ],
  
  [ 
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"], 
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"],  
    ["-has degree rel2","in","?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"]
  ],
  */
  
  // == 9. DEGREE INTENSITY AXIOMS ==

  // --- Property Intensity Bridges ---

  // If a property is high intensity, it satisfies the plain property (high -> none)
  [
    ["-has degree property", "?:W", "?:X", "high", "?:RC", "?:Ctxt"],
    ["has degree property", "?:W", "?:X", "none", "?:RC", "?:Ctxt"]
  ],

  // If a property is low intensity, it satisfies the plain property (low -> none)
  [
    ["-has degree property", "?:W", "?:X", "low", "?:RC", "?:Ctxt"],
    ["has degree property", "?:W", "?:X", "none", "?:RC", "?:Ctxt"]
  ],

  // A property cannot be both high and low intensity (Contradiction)
  [
    ["-has degree property", "?:W", "?:X", "high", "?:RC", "?:Ctxt"],
    ["-has degree property", "?:W", "?:X", "low", "?:RC", "?:Ctxt"]
  ],

  // --- Relation Intensity Bridges ---

  // If a relation is high intensity, it satisfies the plain relation (high -> none)
  [
    ["-has degree rel2", "?:W", "?:X", "?:Y", "high", "?:RC", "?:Ctxt"],
    ["has degree rel2", "?:W", "?:X", "?:Y", "none", "?:RC", "?:Ctxt"]
  ],

  // If a relation is low intensity, it satisfies the plain relation (low -> none)
  [
    ["-has degree rel2", "?:W", "?:X", "?:Y", "low", "?:RC", "?:Ctxt"],
    ["has degree rel2", "?:W", "?:X", "?:Y", "none", "?:RC", "?:Ctxt"]
  ],

  // A relation cannot be both high and low intensity (Contradiction)
  [
    ["-has degree rel2", "?:W", "?:X", "?:Y", "high", "?:RC", "?:Ctxt"],
    ["-has degree rel2", "?:W", "?:X", "?:Y", "low", "?:RC", "?:Ctxt"]
  ],

  // == 3. GRADABLE RELATIONS (TRANSITIVITY & LOGIC) ==
  // Transitivity for TRUE comparative relations only (degree=high/more/less).
  // Intentionally excludes degree="none" (binary relations like "afraid of")
  // to avoid spurious transitive chains. [cite: 350, 357]
  [
    ["-has degree rel2", "?:R", "?:X", "?:Y", "high", "?:Rel", "?:Ctxt"],
    ["-has degree rel2", "?:R", "?:Y", "?:Z", "high", "?:Rel", "?:Ctxt"],
    ["has degree rel2", "?:R", "?:X", "?:Z", "high", "?:Rel", "?:Ctxt"]
  ],
  [
    ["-has degree rel2", "?:R", "?:X", "?:Y", "more", "?:Rel", "?:Ctxt"],
    ["-has degree rel2", "?:R", "?:Y", "?:Z", "more", "?:Rel", "?:Ctxt"],
    ["has degree rel2", "?:R", "?:X", "?:Z", "more", "?:Rel", "?:Ctxt"]
  ],
  [
    ["-has degree rel2", "?:R", "?:X", "?:Y", "less", "?:Rel", "?:Ctxt"],
    ["-has degree rel2", "?:R", "?:Y", "?:Z", "less", "?:Rel", "?:Ctxt"],
    ["has degree rel2", "?:R", "?:X", "?:Z", "less", "?:Rel", "?:Ctxt"]
  ],
  // Comparative to Property Bridge: If X is taller than Y, then X is tall [cite: 345, 355]
  [
    ["-has degree rel2", "?:R", "?:X", "?:Y", "?:Deg", "?:Rel", "?:Ctxt"],
    ["has degree property", "?:R", "?:X", "none", "?:Rel", "?:Ctxt"]
  ],

  // == 3.1 COMPARATIVE ASYMMETRY ==
  // A strict comparative cannot hold in both directions simultaneously.
  // fast(X,Y,high) ∧ fast(Y,X,high) → contradiction
  [
    ["-has degree rel2", "?:R", "?:X", "?:Y", "high", "?:RC1", "?:C1"],
    ["-has degree rel2", "?:R", "?:Y", "?:X", "high", "?:RC2", "?:C2"]
  ],
  // Strict measurement order is asymmetric: less(M1,M2) ∧ less(M2,M1) → contradiction
  [
    ["-less_measure", "?:M1", "?:M2"],
    ["-less_measure", "?:M2", "?:M1"]
  ],
  // Equal measures exclude strict ordering in both directions.
  [
    ["-=", "?:M1", "?:M2"],
    ["-less_measure", "?:M1", "?:M2"]
  ],
  [
    ["-=", "?:M1", "?:M2"],
    ["-less_measure", "?:M2", "?:M1"]
  ],

  // measure_of -> "<noun> of" relational bridge: now injected DYNAMICALLY,
  // per measure noun, by lc_post_inject.inject_measure_relation_bridges — one
  // bridge is added only when BOTH a $measure_of(<noun>,...) fact and an
  // is_rel2 "<noun> of" atom appear in the problem, instead of carrying a
  // static bridge for every measure noun here.  The former static block was:
  //   [ ["-=", ["$measure_of", "length", "?:S", "?:W"], "?:V"],
  //     ["is rel2", "length of", "?:V", "?:S", "?:Ctxt"] ]   (and price/weight/height)

  // event -> "is rel2" bridge for "like"
  /*
  [
    ["isa","activity","?:E"],
    ["-has type", "?:E", "like", "?:Ctxt"],
    ["-has actor", "?:E", "?:X", "?:Ctxt"],
    ["-has target", "?:E", "?:Y", "?:Ctxt"],
    ["is rel2", "like", "?:X", "?:Y", "?:Ctxt"]
  ],
  */
   [
    ["-isa","activity","?:E"],
    ["-has type", "?:E", "like", ["$ctxt","?:T1","?:W","?:Fv3","?:Fv4"]],
    ["-has actor", "?:E", "?:X", ["$ctxt","?:T1","?:W","?:Fv3","?:Fv4"]],
    ["-has target", "?:E", "?:Y", ["$ctxt","?:T1","?:W","?:Fv3","?:Fv4"]],
    ["-has time", "?:E", "?:T2", "?:Prep_t", ["$ctxt","?:T3","?:W","?:Fv3","?:Fv4"]],
    ["is rel2", "like", "?:X", "?:Y", ["$ctxt","?:T2","?:W","?:Fv3","?:Fv4"]]
  ],

  /*  
  [
    ["isa","activity","?:E"],
    ["-has type", "?:E", "like", "?:Ctxt"],
    ["-has actor", "?:E", "?:X", "?:Ctxt"],
    ["-has target", "?:E", "?:Y", "?:Ctxt"],
    ["has degree rel2", "like", "?:X", "?:Y", "none", "?:Cl", "?:Ctxt"] 
  ],
  */
  
  // == 4. SPATIAL & CATEGORICAL TRANSITIVITY ==
  // Transitivity for non-gradable "is rel2" relations [cite: 352, 353]
  [["-is rel2", "in", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "in", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "in", "?:X", "?:Z", "?:Ctxt"]],
  //[["-is rel2", "on", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "on", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "on", "?:X", "?:Z", "?:Ctxt"]],
  [["-is rel2", "inside", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "inside", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "inside", "?:X", "?:Z", "?:Ctxt"]],
  [["-is rel2", "located in", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "located in", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "located in", "?:X", "?:Z", "?:Ctxt"]],
  [["-is rel2", "connected to", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "connected to", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "connected to", "?:X", "?:Z", "?:Ctxt"]],
  [["-is rel2", "part of", "?:X", "?:Y", "?:Ctxt"], ["-is rel2", "part of", "?:Y", "?:Z", "?:Ctxt"], ["is rel2", "part of", "?:X", "?:Z", "?:Ctxt"]],
  // "contains" is the converse of "in": A contains B ↔ B is in A
  [["-is rel2", "contains", "?:A", "?:B", "?:Ctxt"], ["is rel2", "in", "?:B", "?:A", "?:Ctxt"]],
  [["-is rel2", "in", "?:B", "?:A", "?:Ctxt"], ["is rel2", "contains", "?:A", "?:B", "?:Ctxt"]],
  
  // Spatial hierarchy: "on" and "in" both imply "at" (general co-location).
  // "on" does NOT imply "in" (surface contact ≠ containment).
  [["-is rel2", "on", "?:X", "?:Y", "?:Ctxt"], ["is rel2", "at", "?:X", "?:Y", "?:Ctxt"]],
  [["-is rel2", "in", "?:X", "?:Y", "?:Ctxt"], ["is rel2", "at", "?:X", "?:Y", "?:Ctxt"]],

  // == 5. ACTIVITY & MOVEMENT (BAbI TASK LOGIC) ==
  //
  // Davidsonian Activity Reification: every event is shape
  //   isa(activity, E, Ctxt) + has_type(E, V, Ctxt) + has_actor(E, X, Ctxt)
  // with EXACTLY ONE arity-1 modal classifier flagging the event's mode:
  //   ["actuality", E]   - real event (pipeline-injected, never from Stage 2)
  //   ["typical", E]     - habitual / generic
  //   ["capability", E]  - "can / be able to"
  //   ["necessity", E]   - "must / have to"
  //   ["obligation", E]  - "should / ought to"
  //   ["volition", E]    - "want / desire"        (outer of two-event reif.)
  //   ["intention", E]   - "intend / plan"        (outer of two-event reif.)
  //   ["expectation", E] - "expect / anticipate"  (outer of two-event reif.)
  //   ["speech_act", E]  - "say / tell / order"   (outer of two-event reif.)
  // Inner content events (E2 in two-event reifications) carry no classifier.

  // -- 5.1 Modal Classifier Bridge: actuality -> capability (defeasible) --
  //
  // An actual event entails capability for the same actor on the same
  // verb.  Defeasible: a strict ¬capability(E) (e.g., "Penguins cannot
  // fly") overrides via $block.
  //
  // Gated on actuality(E) — the pipeline-injected marker that fires only
  // on real events.  Modal events (typical/capability/necessity/...) and
  // inner content events of two-event reifications carry a different
  // classifier (or none) and are skipped by construction.

  [["-actuality", "?:E"],
   ["-has type", "?:E", "?:V", "?:Ctxt"],
   ["-has actor", "?:E", "?:X", "?:Ctxt"],
   ["capability", "?:E"],
   ["$block", 0, ["$not", ["capability", "?:E"]]]],

  // -- 5.1b Modal Classifier Bridge: typical -> capability (strict) --
  //
  // A habitual/generic event entails capability (if X habitually eats berries,
  // X can eat berries).  Contrapositively, ¬capability(E) defeats typical(E):
  // "Baby bears cannot eat berries" (strict ¬capability) overrides the generic
  // default "Bears eat berries" (defeasible typical) for a baby bear, so a baby
  // bear is excluded from "Who eats berries?" (case 1476).  Strict so the
  // capability negation beats the defeasible typical default.
  // typical carries a $ctxt (arity 2); capability is arity 1.
  [["-typical", "?:E", "?:Ctxt"],
   ["capability", "?:E"]],


  // -- 5.2 Factive content bridge for assertive speech acts (defeasible) --
  //
  // For an outer speech_act event E1 whose verb is one of the assertive
  // verbs (say/claim/report/state/announce), the inner content event E2
  // (linked by has_content) is defeasibly actual.  Closes case 159:
  // "John said that Mary left.  Mary left?" -> Probably true (~0.9).
  //
  // Per-verb gating (instead of "?:V" free) keeps directive verbs
  // (ask/order/request), commissive verbs (promise/threaten/vow), and
  // expressive verbs (apologize/thank) out of scope -- those do NOT entail
  // their content.  Excludes "tell" because Stage-2 reifies both
  // "told that X" (assertive) and "told to V" (directive) as
  // speech_act + has_content + has_type=tell with no syntactic distinction.
  //
  // Confidence 0.9 with the standard $block guard so a contradicting
  // assertion can defeat the inference ("John lied that Mary left.").

  { "@confidence": 0.9, "@logic": [
    ["-speech_act", "?:E1"],
    ["-has content", "?:E1", "?:E2"],
    ["-has type", "?:E1", "say", "?:Ct"],
    ["actuality", "?:E2"],
    ["$block", 0, ["$not", ["actuality", "?:E2"]]]
  ] },
  { "@confidence": 0.9, "@logic": [
    ["-speech_act", "?:E1"],
    ["-has content", "?:E1", "?:E2"],
    ["-has type", "?:E1", "claim", "?:Ct"],
    ["actuality", "?:E2"],
    ["$block", 0, ["$not", ["actuality", "?:E2"]]]
  ] },
  { "@confidence": 0.9, "@logic": [
    ["-speech_act", "?:E1"],
    ["-has content", "?:E1", "?:E2"],
    ["-has type", "?:E1", "report", "?:Ct"],
    ["actuality", "?:E2"],
    ["$block", 0, ["$not", ["actuality", "?:E2"]]]
  ] },
  { "@confidence": 0.9, "@logic": [
    ["-speech_act", "?:E1"],
    ["-has content", "?:E1", "?:E2"],
    ["-has type", "?:E1", "state", "?:Ct"],
    ["actuality", "?:E2"],
    ["$block", 0, ["$not", ["actuality", "?:E2"]]]
  ] },
  { "@confidence": 0.9, "@logic": [
    ["-speech_act", "?:E1"],
    ["-has content", "?:E1", "?:E2"],
    ["-has type", "?:E1", "announce", "?:Ct"],
    ["actuality", "?:E2"],
    ["$block", 0, ["$not", ["actuality", "?:E2"]]]
  ] },

  // -- 5.2b Negative implicative bridge: refuse/decline to V -> ¬(actual V) --
  // Now injected DYNAMICALLY by lc_post_inject.inject_negative_implicative_bridges
  // (one clause per verb, only when "refuse"/"decline" appears in the problem),
  // instead of carrying a static clause here.  The former static block was:
  //   [ ["-has type", "?:E1", "refuse", "?:Ct1"],
  //     ["-has content", "?:E1", "?:E2"],
  //     ["-has type",   "?:E2", "?:V", "?:Ct2"], ["-has actor",  "?:E2", "?:X", "?:Ct2"],
  //     ["-has target", "?:E2", "?:Y", "?:Ct2"],
  //     ["-has type",   "?:E3", "?:V", "?:Ct3"], ["-has actor",  "?:E3", "?:X", "?:Ct3"],
  //     ["-has target", "?:E3", "?:Y", "?:Ct3"], ["-actuality",  "?:E3"] ]
  // i.e. "Tom refused to eat the soup" -> there is no actual eat(Tom,soup) -> the
  // query "Tom ate the soup?" is False (not just Unknown); case 1597.


  // Movement Results: If X 'go'es to Dest, X is 'at' Dest in the next state [cite: 146, 147]
  // Result tense is "present" (at the new world), not copied from the source event.
  // Uses variable worlds with next(?:W, ?:W2) precondition.
  [
    ["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has type", "?:E", "go", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has destination", "?:E", "?:Dest", "?:Prep", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-next", "?:W", "?:W2"],
    ["is rel2", "at", "?:X", "?:Dest", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],
  // Movement also works with has_direction (synonym for has_destination in some parses)
  [
    ["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has type", "?:E", "go", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has direction", "?:E", "?:Dest", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-next", "?:W", "?:W2"],
    ["is rel2", "at", "?:X", "?:Dest", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],
  /*
  // Movement retraction (OLD, replaced by moved+$block approach):
  // after moving to Dest, X is no longer at any previous location Y
  // (unless Y = Dest, i.e. moved to the same place). This provides evidence for $block
  // on the frame axiom, preventing old locations from persisting.
  [
    ["-is rel2", "at", "?:X", "?:Y", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has actor", "?:E", "?:X", ["$ctxt", "?:T2", "?:W", "?:L2", "?:K2"]],
    ["-has type", "?:E", "go", ["$ctxt", "?:T2", "?:W", "?:L2", "?:K2"]],
    ["-has destination", "?:E", "?:Dest", "?:Prep", ["$ctxt", "?:T2", "?:W", "?:L2", "?:K2"]],
    ["-next", "?:W", "?:W2"],
    ["=", "?:Y", "?:Dest"],
    ["-is rel2", "at", "?:X", "?:Y", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],
  */

  // Derive moved(X, W): X performed a movement event at world W.
  // Used by the is_rel2 frame axiom to block location persistence when X moved.
  // Only the "go" version is needed: lc_rewrites.py normalizes travel/journey/
  // move to "go" before clauses reach the prover (avoids synonym axiom chains).
  [["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["-has type", "?:E", "go", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["moved", "?:X", "?:W"]],

  // Derive moved_between(X, W_old, W_new): X performed a movement at some world
  // strictly between W_old and W_new. Used to block §12 is_rel2 tense-migration
  // of a present-tense location when the actor moved AGAIN after the source
  // world (the existing moved(X,W_old) block only catches a move AT the source).
  // Case 1327: Sandra is at hallway (present W2), then moves to garden at W3;
  // without this, the stale hallway migrated to past W4 and leaked into the
  // "Where is Sandra?" answer alongside the correct garden.
  [["-moved", "?:X", "?:Wmid"],
   ["-before", "?:W_old", "?:Wmid"],
   ["-before", "?:Wmid", "?:W_new"],
   ["moved_between", "?:X", "?:W_old", "?:W_new"]],
  /*
  // Redundant with pipeline normalization in lc_rewrites.py:
  [["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["-has type", "?:E", "travel", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["moved", "?:X", "?:W"]],
  [["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["-has type", "?:E", "journey", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["moved", "?:X", "?:W"]],
  [["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["-has type", "?:E", "move", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["moved", "?:X", "?:W"]],
  */

  // Movement Synonyms — REDUNDANT, kept commented for documentation.
  // lc_rewrites.py rewrites travel/journey/move → go pre-clausification,
  // so the prover never sees these verbs. Pipeline normalization avoids
  // synonym axiom chains that cause combinatorial explosion with many worlds.
  /*
  [["-has type", "?:E", "travel", "?:Ctxt"], ["has type", "?:E", "go", "?:Ctxt"]],
  [["-has type", "?:E", "journey", "?:Ctxt"], ["has type", "?:E", "go", "?:Ctxt"]],
  [["-has type", "?:E", "move", "?:Ctxt"], ["has type", "?:E", "go", "?:Ctxt"]],
  */

  // Placement Results: If X 'put's Target at Dest, Target is 'at' Dest in the next state.
  // Mirrors the movement result axiom above, but the TARGET (not the actor) ends
  // up at the destination. Pattern: "Tom put the book on the chair" → book is at chair.
  [
    ["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has type", "?:E", "put", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has target", "?:E", "?:Obj", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has destination", "?:E", "?:Dest", "?:Prep", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-next", "?:W", "?:W2"],
    ["is rel2", "?:Prep", "?:Obj", "?:Dest", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],

  // == 5b. TRANSFER RESULTS ==
  // If X 'give's Target to Recipient, Recipient 'have's Target in the next state.
  // Pattern follows movement result axiom above.
  [
    ["-has actor", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has type", "?:E", "give", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has recipient", "?:E", "?:Recip", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has target", "?:E", "?:Obj", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-next", "?:W", "?:W2"],
    ["have", "?:Recip", "?:Obj", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],

  // Derive transferred(Obj, W): object was transferred away at world W.
  // Used by "have" frame axiom to block giver's possession from persisting.
  [["-has type", "?:E", "give", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["-has target", "?:E", "?:Obj", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
   ["transferred", "?:Obj", "?:W"]],

  // == 5c. PERSPECTIVE BRIDGES (GIVE/RECEIVE) ==
  // Give and receive describe the same event from different perspectives.
  // Only give→receive direction to avoid circular role pollution.
  // (receive→give is handled by pipeline normalization in lc_rewrites.py.)
  // Type bridge: a give event is also a receive event.
  [["-has type", "?:E", "give", "?:Ctxt"],
   ["has type", "?:E", "receive", "?:Ctxt"]],
  // Role mapping: the recipient of the give is the actor of the receive.
  [["-has type", "?:E", "give", "?:Ctxt"],
   ["-has recipient", "?:E", "?:X", "?:Ctxt"],
   ["has actor", "?:E", "?:X", "?:Ctxt"]],

  // Transfer verb synonyms — hand/send → give are still rewritten in
  // lc_rewrites.py pre-clausification. "pass" is no longer rewritten there
  // because it has too many non-transfer senses (pass an exam, pass by, ...);
  // instead we bridge defeasibly here so the give-axiom chain remains
  // available when "pass" really does mean transfer.
  {
    "@confidence": 0.85,
    "@logic": [
      ["-has type", "?:E", "pass", "?:Ctxt"],
      ["has type", "?:E", "give", "?:Ctxt"],
      ["$block", 0, ["$not", ["has type", "?:E", "give", "?:Ctxt"]]]
    ]
  },

  // == 5d. COMPLETION RESULT STATES ==
  // If a "finish" event targets X, then X has property "finished" in the next state.
  [
    ["-has type", "?:E", "finish", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-has target", "?:E", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
    ["-next", "?:W", "?:W2"],
    ["has property", "finished", "?:X", ["$ctxt", "present", "?:W2", "?:L", "?:K"]]
  ],

  // Stative "keep": "Eve kept the milk in the fridge" → normally the milk
  // is in the fridge in the same world (keep is durative, not transitional —
  // no next() chain). Higher confidence than the generic PP-attachment
  // bridge below because "keep" lexicalises the stative-result reading.
  // Two sibling axioms, since LLMs vary on whether they emit the locative PP
  // as has_location (gemini, claude) or has_destination (deepseek).
  {
    "@confidence": 0.95,
    "@logic": [
      ["-has type", "?:E", "keep", "?:Ctxt"],
      ["-has target", "?:E", "?:Obj", "?:Ctxt"],
      ["-has location", "?:E", "?:Loc", "?:Prep", "?:Ctxt"],
      ["is rel2", "?:Prep", "?:Obj", "?:Loc", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "?:Prep", "?:Obj", "?:Loc", "?:Ctxt"]]]
    ]
  },
  {
    "@confidence": 0.95,
    "@logic": [
      ["-has type", "?:E", "keep", "?:Ctxt"],
      ["-has target", "?:E", "?:Obj", "?:Ctxt"],
      ["-has destination", "?:E", "?:Loc", "?:Prep", "?:Ctxt"],
      ["is rel2", "?:Prep", "?:Obj", "?:Loc", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "?:Prep", "?:Obj", "?:Loc", "?:Ctxt"]]]
    ]
  },

  // == 5e. PP-ATTACHMENT BRIDGES ==
  // Bridge: instrument implies possession by the actor (defeasible, 90%).
  // "The man saw the woman with a telescope" → the man had the telescope.
  {
    "@confidence": 0.9,
    "@logic": [
      ["-has instrument", "?:E", "?:X", "?:Ctxt"],
      ["-has actor", "?:E", "?:Y", "?:Ctxt"],
      ["have", "?:Y", "?:X", "?:Ctxt"],
      ["$block", 0, ["$not", ["have", "?:Y", "?:X", "?:Ctxt"]]]
    ]
  },
  // Bridge: event location implies target location (defeasible, 90%).
  // "John ate the pizza on the table" → the pizza was on the table.
  {
    "@confidence": 0.9,
    "@logic": [
      ["-has location", "?:E", "?:L", "?:P", "?:Ctxt"],
      ["-has target", "?:E", "?:Y", "?:Ctxt"],
      ["is rel2", "?:P", "?:Y", "?:L", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "?:P", "?:Y", "?:L", "?:Ctxt"]]]
    ]
  },
  // Bridge: event location implies ACTOR location for containment/proximity
  // prepositions (in / at).  "The children playing in the garden" → the
  // children were in the garden; "Mike ate berries in the forest" → Mike was
  // in the forest.  Restricted to in/at: with support prepositions (on/under)
  // the location attaches to the target, not the actor ("ate the pizza on the
  // table" does NOT put John on the table — that case is handled by the target
  // bridge above).  Two sibling axioms, one per safe preposition.
  {
    "@confidence": 0.9,
    "@logic": [
      ["-has location", "?:E", "?:L", "in", "?:Ctxt"],
      ["-has actor", "?:E", "?:X", "?:Ctxt"],
      ["is rel2", "in", "?:X", "?:L", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "in", "?:X", "?:L", "?:Ctxt"]]]
    ]
  },
  {
    "@confidence": 0.9,
    "@logic": [
      ["-has location", "?:E", "?:L", "at", "?:Ctxt"],
      ["-has actor", "?:E", "?:X", "?:Ctxt"],
      ["is rel2", "at", "?:X", "?:L", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "at", "?:X", "?:L", "?:Ctxt"]]]
    ]
  },
  // Bridge: event location implies ACTOR location for POSITIONAL prepositions
  // (behind / in_front_of / beside / next_to / near / by / left_of / right_of).
  // Like in/at, these locate the actor AT a position relative to the landmark,
  // so when an event HAS a location (not a destination) with such a preposition
  // the actor is there: "the car parked behind the house" → the car is behind
  // the house (case 670, has_actor reading). Support preps (on/under) attach to
  // the target instead, so they are excluded.
  //
  // These are now injected DYNAMICALLY — one bridge per positional preposition
  // that actually appears in a has_location atom — by
  // lc_post_inject.inject_positional_actor_bridges (wired in logconvert), so
  // the prover only carries the relevant ones. The static forms are kept here,
  // commented out, as documentation of the canonical shape:
  //
  // for PREP in {behind, in_front_of, beside, next_to, near, by, left_of, right_of}:
  //   { "@confidence": 0.9, "@logic": [
  //       ["-has location", "?:E", "?:L", PREP, "?:Ctxt"],
  //       ["-has actor", "?:E", "?:X", "?:Ctxt"],
  //       ["is rel2", PREP, "?:X", "?:L", "?:Ctxt"],
  //       ["$block", 0, ["$not", ["is rel2", PREP, "?:X", "?:L", "?:Ctxt"]]] ] }

  // == 6. PERSISTENCE (FRAME PROBLEM) ==
  // Default persistence across world states using variable worlds with next(?:W, ?:W2).
  // Each predicate persists defeasibly ($block) unless overridden.

  /*
  // is rel2 (OLD: general $not block — replaced by moved-based block)
  {
    "@confidence": 0.99,
    "@logic": [
      ["-is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]]]]
    ]
  },
  */

  // is rel2 persistence: blocked when X moved (go-event) at that world.
  // This prevents old locations from persisting after movement while allowing
  // non-movement is_rel2 relations (like "afraid of") to persist normally
  // (since moved(X,W) is only derived from go-events, not from other relations).
  {
    "@confidence": 0.99,
    "@logic": [
      ["-is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["moved", "?:X", "?:W"]]
    ]
  },

  // have: blocked when the possessed object was transferred at that world.
  {
    "@confidence": 0.99,
    "@logic": [
      ["-have", "?:Y", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["have", "?:Y", "?:X", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["transferred", "?:X", "?:W"]]
    ]
  },
  // has property
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has property", "?:P", "?:X", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["has property", "?:P", "?:X", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has property", "?:P", "?:X", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]]]]
    ]
  },
  // has degree property
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has degree property", "?:P", "?:X", "?:D", "?:C", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["has degree property", "?:P", "?:X", "?:D", "?:C", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has degree property", "?:P", "?:X", "?:D", "?:C", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]]]]
    ]
  },
  // has part
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has part", "?:X", "?:Y", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["has part", "?:X", "?:Y", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has part", "?:X", "?:Y", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]]]]
    ]
  },
  // has degree rel2
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]],
      ["-next", "?:W", "?:W2"],
      ["has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "?:T", "?:W2", "?:L", "?:K"]]]]
    ]
  },

  // == 6a. SAME-WORLD TENSE BRIDGE: past@W → present@W (defeasible) ==
  // DISABLED: replaced by question-specific bridge axioms generated in
  // logconvert.py (build_question_tense_bridges). The dynamic axioms
  // pin entity arguments to what the question actually mentions, so the
  // prover only chains past->present for those specific entities — much
  // smaller search space than the global axioms below.
  /*
  // have
  {
    "@confidence": 0.97,
    "@logic": [
      ["-have", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["have", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["have", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // has part
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has part", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["has part", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has part", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // can
  {
    "@confidence": 0.99,
    "@logic": [
      ["-can", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["can", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["can", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // has property
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has property", "?:P", "?:X", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["has property", "?:P", "?:X", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has property", "?:P", "?:X", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // has degree property
  {
    "@confidence": 0.99,
    "@logic": [
      ["-has degree property", "?:P", "?:X", "?:D", "?:RC", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["has degree property", "?:P", "?:X", "?:D", "?:RC", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has degree property", "?:P", "?:X", "?:D", "?:RC", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // is rel2
  {
    "@confidence": 0.95,
    "@logic": [
      ["-is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  // has degree rel2
  {
    "@confidence": 0.95,
    "@logic": [
      ["-has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "past", "?:W", "?:L", "?:K"]],
      ["has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
      ["$block", 0, ["$not", ["has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "present", "?:W", "?:L", "?:K"]]]]
    ]
  },
  */

  /*
  // == 6b. SPATIAL MUTUAL EXCLUSION (experimental, commented out) ==
  // If X is at two locations at the same world, and both are rooms of specific
  // types known to be different, then they must be equal (contradiction via
  // inequality facts).  Requires inequality axioms between room classes.

  // Exclusion: two room locations for same person at same world must be equal
  {"@logic": [
    ["=", "?:Loc1", "?:Loc2"],
    ["-isa", "room", "?:Loc1"],
    ["-isa", "room", "?:Loc2"],
    ["-is rel2", "at", "?:X", "?:Loc1", ["$ctxt", "present", "?:W", "?:L", "?:K"]],
    ["-is rel2", "at", "?:X", "?:Loc2", ["$ctxt", "present", "?:W", "?:L", "?:K"]]
  ], "@name": "ax_room_exclusion"},

  // Room class inequality: entities of different room classes are distinct.
  // These would need to be generated programmatically for each pair of room
  // classes present in the input, or derived from a taxonomy.
  // Example pairs (would be generated per problem):
  [
    ["-isa", "hallway", "?:X"],
    ["-isa", "kitchen", "?:Y"],
    ["-=", "?:X", "?:Y"]
  ],
  [
    ["-isa", "hallway", "?:X"],
    ["-isa", "bathroom", "?:Y"],
    ["-=", "?:X", "?:Y"]
  ],
  [
    ["-isa", "kitchen", "?:X"],
    ["-isa", "bathroom", "?:Y"],
    ["-=", "?:X", "?:Y"]
  ],
  // Also need: isa(room, X) for each location entity — could be generated
  // from the isa(hallway, X) etc. via a superclass axiom:
  [["-isa", "hallway", "?:X"], ["isa", "room", "?:X"]],
  [["-isa", "kitchen", "?:X"], ["isa", "room", "?:X"]],
  [["-isa", "bathroom", "?:X"], ["isa", "room", "?:X"]],
  [["-isa", "bedroom", "?:X"], ["isa", "room", "?:X"]],
  [["-isa", "garden", "?:X"], ["isa", "room", "?:X"]],
  [["-isa", "office", "?:X"], ["isa", "room", "?:X"]],
  */

  // == 7. SETS & COUNTING ==
  // Subset Cardinality: |A ∩ B| <= |A| [cite: 355]
  [
    ["=", "?:N", ["$count", ["$setof", ["and", "?:X1", "?:X2"], "?:Y1"]]],
    ["=>", ["$greatereq", ["$count", ["$setof", "?:X1", "?:Y1"]], "?:N"]]
  ],
  // Two-condition set cardinality
  [
    ["=", "?:N", ["$count", ["$setof", ["and", "?:X1", "?:X2", "?:X3"], "?:Y1"]]],
    ["=>", ["$greatereq", ["$count", ["$setof", ["and", "?:X1", "?:X2"], "?:Y1"]], "?:N"]]
  ],
  // Three-condition set cardinality
  [
    ["=", "?:N", ["$count", ["$setof", ["and", "?:X1", "?:X2", "?:X3", "?:X4"], "?:Y1"]]],
    ["=>", ["$greatereq", ["$count", ["$setof", ["and", "?:X1", "?:X2", "?:X3"], "?:Y1"]], "?:N"]]
  ],
  // Set Type Constraint
  [["-member", "?:X", "?:S", "?:Ctxt"], ["-is set of", "?:Type", "?:S", "?:Ctxt"], ["isa", "?:Type", "?:X"]],

  /*
  
  // these two look like failed attempts of the superset counting rule
[
  ["-=", "?:N", ["$count", ["$setof", "?:Var", "?:ID", ["and", "?:P1", "?:P2"]]]],
  ["$greatereq", ["$count", ["$setof", "?:Var", "?:ID", ["and", "?:P1"]]], "?:N"]
],
[
  ["-=", "?:N", ["$count", ["$setof", "?:Var", "?:ID", ["and", "?:P1", "?:P2", "?:P3"]]]],
  ["$greatereq", ["$count", ["$setof", "?:Var", "?:ID", ["and", "?:P1", "?:P2"]]], "?:N"]
],
  
  */
  
  // the size of a superset of some set S is not less than the size of the set S.
  
  [ ["-=","?:X",["$count",["$setof","?:H","?:J",["$and","?:A","?:B"]]]],  ["$greatereq",["$count",["$setof","?:H","?:J",["$and","?:A"]]],"?:X"] ],
  
  [ ["-=","?:X",["$count",["$setof","?:H","?:J",["$and","?:A","?:B","?:C"]]]],  ["$greatereq",["$count",["$setof","?:H","?:J",["$and","?:A","?:B"]]],"?:X"] ],
  
  [ ["-=","?:X",["$count",["$setof","?:H","?:J",["$and","?:A","?:B","?:C"]]]],  ["$greatereq",["$count",["$setof","?:H","?:J",["$and","?:A","?:C"]]],"?:X"] ],
  
  [ ["-=","?:X",["$count",["$setof","?:H","?:J",["$and","?:A","?:B","?:C"]]]],  ["$greatereq",["$count",["$setof","?:H","?:J",["$and","?:A"]]],"?:X"] ],
   
   
/*

[
[["=",2,["$count",["$setof",["isa","car","$arg1"],"c1_John"]]]],

[["-=","?:X",["$count",["$setof",["and","?:Y","?:Z"],"?:U"]]],          ["$greatereq",["$count",["$setof","?:Y","?:U"]],"?:X"]],

[["=",3,["$count",["$setof",["and",["isa","car","$arg1"],["prop","nice","$arg1","$generic","$generic",["$ctxt","Pres",1]]],"c1_John"]]]]
]

John 1 has three nice cars.
  {"@name":"sent_S1","@logic":["isa","person","John 1"]}
  {"@name":"sent_S1","@logic":["=",3,["$count",["$setof","have","John 1",["$and",["$isa","car","$arg1"],["$has_degree_property","nice","$arg1","none","car"]]]]]}
Does John 1 have two cars?
  {"@name":"sent_S2","@logic":[["-$defq0"],["=",2,["$count",["$setof","have","John 1",["$and",["$isa","car","$arg1"]]]]]]}
  {"@name":"sent_S2","@logic":[["-=",2,["$count",["$setof","have","John 1",["$and",["$isa","car","$arg1"]]]]],["$defq0"]]}
  {"@name":"sent_S2","@question":["$defq0"]}

[

["=",3,["$count",["$setof","h","j",["$and","a","b"]]]],
["-=",2,["$count",["$setof","h","j",["$and","a"]]]],

[  ["-=",3,["$count",["$setof","h","j",["$and","a","b"]]]],
   ["$greatereq",["$count",["$setof","h","j",["$and","a"]]],3] ]

]


[
 [["=",2,"b"]],

 [  ["-=",3,"a"], ["$greatereq","b",3] ],
   
 [["=",3,"a"]]   
]

[
 [["=",2,["$count",["$setof","cc","ee"]]]],

 [["-=","?:X",["$count",["$setof",["and","?:Y","?:Z"],"?:U"]]], ["$greatereq",["$count",["$setof","?:Y","?:U"]],"?:X"]],

 [["=",3,["$count",["$setof",["and","cc","dd"],"ee"]]]]
]


[
 [["=",2,["$count","s2"]]],

 [["-=","?:X",["$count","s1"]], ["$greatereq",["$count","s2"],"?:X"]],

 [["=",3,["$count","s1"]]]
]

[
 ["=",2,["$count",["$setof","h","j",["$and","a"]]]],
 
 [ ["-=","?:X",["$count",["$setof","h","j",["$and","a","b"]]]],  ["$greatereq",["$count",["$setof","h","j",["$and","a"]]],"?:X"] ],
   
 ["=",3,["$count",["$setof","h","j",["$and","a","b"]]]]
 
]

[
 [["=",2,["$count",["$setof","have","John 1",["$and",["$isa","car","$arg1"]]]]]],
 
 [ ["-=","?:X",["$count",["$setof","?:H","?:J",["$and","?:A","?:B"]]]],  ["$greatereq",["$count",["$setof","?:H","?:J",["$and","?:A"]]],"?:X"] ],

 ["=",3,["$count",["$setof","have","John 1",["$and",["$isa","car","$arg1"],["$has_degree_property","nice","$arg1","none","car"]]]]]
]

*/


  // == 7b. DEFINITE FUNCTION TERMS ($theof1) ==
  // Note: both the isa and the have bridges are generated per-relation at
  // parse time (isa in logconvert, have via add_possessive_have) so that
  // they are grounded to concrete owners. A generic have bridge like
  //   [["have", "?:S", ["$theof1", "?:R", "?:S", "?:C"], "?:C"]]
  // is universally quantified in S and lets the prover answer any
  // wh-query about possession with a free-variable witness (e.g. "X3"
  // alongside "Tom" for "who had a bicycle?"), so it is intentionally
  // NOT defined here.

  // == 7c. PREPOSITION SUBSUMPTION (spatial) ==
  // Unidirectional specific → general implications for near-synonymous
  // spatial prepositions. "X is under Y" implies "X is below Y", but not
  // vice versa ("below" is more general — no contact implication).
  // Mutual-exclusion between opposites lives below (§7e) as static axioms.
  [["-is rel2", "underneath", "?:X", "?:Y", "?:C"], ["is rel2", "below", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "beneath",    "?:X", "?:Y", "?:C"], ["is rel2", "below", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "under",      "?:X", "?:Y", "?:C"], ["is rel2", "below", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "over",       "?:X", "?:Y", "?:C"], ["is rel2", "above", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "on_top_of",  "?:X", "?:Y", "?:C"], ["is rel2", "above", "?:X", "?:Y", "?:C"]],

  // == 7d. PREPOSITION SUBSUMPTION (temporal) ==
  [["-is rel2", "prior_to",   "?:X", "?:Y", "?:C"], ["is rel2", "before", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "following",  "?:X", "?:Y", "?:C"], ["is rel2", "after",  "?:X", "?:Y", "?:C"]],
  [["-is rel2", "preceding",  "?:X", "?:Y", "?:C"], ["is rel2", "before", "?:X", "?:Y", "?:C"]],

  // == 7e. PREPOSITION MUTUAL EXCLUSION ==
  // Permanent mutual-exclusion between opposite preposition pairs. These
  // are first-class predicates in the standard ontology (they appear as
  // subsumption targets in §7c/7d), so the exclusions hold universally
  // and are emitted statically here rather than by inject_exclusion_axioms.
  // Spatial:
  [["-is rel2", "above",       "?:X", "?:Y", "?:C"], ["-is rel2", "below",       "?:X", "?:Y", "?:C"]],
  [["-is rel2", "over",        "?:X", "?:Y", "?:C"], ["-is rel2", "under",       "?:X", "?:Y", "?:C"]],
  [["-is rel2", "behind",      "?:X", "?:Y", "?:C"], ["-is rel2", "in_front_of", "?:X", "?:Y", "?:C"]],
  [["-is rel2", "inside",      "?:X", "?:Y", "?:C"], ["-is rel2", "outside",     "?:X", "?:Y", "?:C"]],
  [["-is rel2", "left_of",     "?:X", "?:Y", "?:C"], ["-is rel2", "right_of",    "?:X", "?:Y", "?:C"]],
  // "on" excludes "under"/"below" (top-surface contact rules out being below).
  // The (over,under) and (above,below) pairs above already block over/above
  // co-occurrence; "on" needs explicit pairing because it is not subsumed by
  // "above" in §7c (on means top contact, above does not).
  [["-is rel2", "on",          "?:X", "?:Y", "?:C"], ["-is rel2", "under",       "?:X", "?:Y", "?:C"]],
  [["-is rel2", "on",          "?:X", "?:Y", "?:C"], ["-is rel2", "below",       "?:X", "?:Y", "?:C"]],
  // Temporal:
  [["-is rel2", "before",      "?:X", "?:Y", "?:C"], ["-is rel2", "after",       "?:X", "?:Y", "?:C"]],
  // Proximity (gradable: positive side any-degree, antonym side "none"
  // intensity, shared RELCLASS — the high→none / low→none intensity
  // bridges in §9 propagate the negation across all intensities).
  [
    ["-has degree rel2", "near",     "?:X", "?:Y", "?:D",  "?:RC", "?:C"],
    ["-has degree rel2", "far_from", "?:X", "?:Y", "none", "?:RC", "?:C"]
  ],
  [
    ["-has degree rel2", "far_from", "?:X", "?:Y", "?:D",  "?:RC", "?:C"],
    ["-has degree rel2", "near",     "?:X", "?:Y", "none", "?:RC", "?:C"]
  ],

  // == 7f. CARRIER TRANSPARENCY ==
  // If C is a carrier (plate, tray, newspaper, ...), X is on C, and C is
  // on S, then X is also on S. Defeasible at 0.85 so an explicit
  // ¬is_rel2(on, X, S) defeats the bridge.
  // "The pizza is on the plate. The plate is on the table." => pizza on table.
  // The carrier tag itself is emitted dynamically from lc_post_inject's
  // inject_carrier_lifts: the per-noun lift `[¬isa(<noun>,X), isa(carrier,X)]`
  // is added only when <noun> appears in input or axiom_vocab.
  {
    "@confidence": 0.85,
    "@logic": [
      ["-isa", "carrier", "?:C", "?:Ctxt"],
      ["-is rel2", "on", "?:X", "?:C", "?:Ctxt"],
      ["-is rel2", "on", "?:C", "?:S", "?:Ctxt"],
      ["is rel2", "on", "?:X", "?:S", "?:Ctxt"],
      ["$block", 0, ["$not", ["is rel2", "on", "?:X", "?:S", "?:Ctxt"]]]
    ]
  },

  // == 7g. DIRECT-SUPPORT UNIQUENESS (X2 with containment escape) ==
  // If X is on Y1 and X is on Y2 in the same context, the targets must
  // be the same — UNLESS one is on or part of the other (allows stacked
  // and sub-part configurations like book-on-table-on-rug or
  // soup-on-stove-on-burner).
  //
  // Strict (no @confidence): under entity UNA via the `#:` prefix
  // (lc_post_una.apply_una), forcing Y1=Y2 on syntactically distinct
  // entity constants gives an immediate contradiction. Closes case
  // 148: "John ate the pizza on the table. Was the pizza on the floor?"
  [
    ["-is rel2", "on", "?:X", "?:Y1", "?:C"],
    ["-is rel2", "on", "?:X", "?:Y2", "?:C"],
    ["=", "?:Y1", "?:Y2"],
    ["$block", 0, ["is rel2", "on",      "?:Y1", "?:Y2", "?:C"]],
    ["$block", 0, ["is rel2", "on",      "?:Y2", "?:Y1", "?:C"]],
    ["$block", 0, ["is rel2", "part of", "?:Y1", "?:Y2", "?:C"]],
    ["$block", 0, ["is rel2", "part of", "?:Y2", "?:Y1", "?:C"]]
  ],

  // == 8. MEASUREMENTS & ATTRIBUTES ==
  // Value Holders [cite: 306, 307]
  [["isa", "weight", ["$theof1", "weight", "?:O", "?:Ctxt"]]],
  [["isa", "price", ["$theof1", "price", "?:O", "?:Ctxt"]]],
  [["isa", "length", ["$theof1", "length", "?:O", "?:Ctxt"]]],
  // Property to Attribute Mapping
  //
  // The single static "red -> color of" stub below is REPLACED by the dynamic
  // lc_post_inject.inject_attribute_relation_bridges (wired in logconvert),
  // which bridges a stored property VALUE to its attribute RELATION for the
  // color / shape / material / taste families (value sets from
  // data_exclusions), in both arg-orders, and -- crucially -- from the
  // has_property form (the stub expected has_degree_property, but colours
  // normalise to has_property, so the stub never fired). Case 901. The stub is
  // kept here commented out as documentation of the canonical shape:
  //
  // [ ["-has degree property", "red", "?:X", "none", "?:Rel", "?:Ctxt"],
  //   ["is rel2", "color of", "red", "?:X", "?:Ctxt"] ],
  
  // == 11. WORLD GRAPH GEOMETRY ==

// Axiom 1: Direct succession implies "before".
//
// The concrete W0..Wn `next` chain that used to live here is now generated
// dynamically by lc_postprocess.inject_world_geometry, based on which world
// constants (W0, W1, ...) actually appear in the per-sentence clauses. Only
// the minimal chain spanning the observed worlds is emitted, so the `before`
// transitivity closure stays small when a problem touches only a few worlds.

[
  ["-next", "?:W_prev", "?:W_curr"],
  ["before", "?:W_prev", "?:W_curr"]
],

// Axiom 2: Transitivity of "before" (W0 < W1, W1 < W2 => W0 < W2)
[
  ["-before", "?:W1", "?:W2"],
  ["-before", "?:W2", "?:W3"],
  ["before", "?:W1", "?:W3"]
],

  // == 12. TENSE MIGRATION BRIDGES ==
/*
[
  ["-has degree rel2","?:R","?:X","?:Y","?:Z","?:U",["$ctxt","present","W0","?:Fv1","?:Fv2"]],
  ["has degree rel2","?:R","?:X","?:Y","?:Z","?:U",["$ctxt","past","W1","?:Fv1","?:Fv2"]]
],
*/
// --- Flat Predicates ---

// has property
[
  ["-has property", "?:P", "?:X", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has property", "?:P", "?:X", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// have
[
  ["-have", "?:O", "?:X", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["have", "?:O", "?:X", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// has part
[
  ["-has part", "?:W", "?:P", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has part", "?:W", "?:P", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// is rel2
//
// HISTORY: previously this axiom had no $block — any present-tense is_rel2
// fact in W_old freely migrated to a past-tense fact at any later W_new.
//
// CHANGE: added $block(0, moved(?:E1, ?:W_old)). The block fires when E1
// (the locatum / first entity argument) performed a movement event at
// W_old; in that case the present-tense fact about E1 in W_old has already
// been superseded by the next motion-result and must not project forward
// as a historical fact about later worlds.
//
// WHY: case 197 ("Sandra travelled to the kitchen. Sandra travelled to the
// hallway. Where is Sandra?") was returning BOTH "at hallway" and "at
// kitchen" because:
//   1. motion-result from sk0 derived  is_rel2 at Sandra kitchen [present W1]
//   2. this axiom (no block) migrated to is_rel2 at Sandra kitchen [past W2]
//   3. the dynamic question_bridge (lc_ctxt.build_question_tense_bridges)
//      defeasibly converted past W2 → present W2
//   4. the goal "where is Sandra in present W2" matched the stale kitchen
//      location in addition to the correct hallway location.
// The is_rel2 PERSISTENCE axiom (above, §6) already blocks on moved(?:X,?:W)
// for the same reason — this brings tense-migration in line.
//
// LIMITATION: Past-location queries about moved entities ("Was Sandra
// at the kitchen?" asked at W2) lose this migration path. They fall
// back to a direct past-tense assertion or the same-world
// question_bridge.
//
// SCOPE: only is_rel2 — the other §12 migration axioms (has_property,
// have, has_part, can, has_degree_*, has_actor, has_target, ...) describe
// things that don't have a "moved" notion in the same sense.
{
  "@confidence": 0.99,
  "@logic": [
    ["-is rel2", "?:R", "?:E1", "?:E2", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
    ["-before", "?:W_old", "?:W_new"],
    ["is rel2", "?:R", "?:E1", "?:E2", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]],
    ["$block", 0, ["moved", "?:E1", "?:W_old"]],
    ["$block", 0, ["moved_between", "?:E1", "?:W_old", "?:W_new"]]
  ]
},

// --- Gradable Predicates ---

// has degree property
[
  ["-has degree property", "?:P", "?:X", "?:D", "?:RC", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has degree property", "?:P", "?:X", "?:D", "?:RC", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// has degree rel2
[
  ["-has degree rel2", "?:R", "?:E1", "?:E2", "?:D", "?:RC", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has degree rel2", "?:R", "?:E1", "?:E2", "?:D", "?:RC", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// --- Davidsonian Roles (Track 2) ---

// isa, has type, has actor, has target
// These propagate the context change to ensure the whole event structure matches.
[
  ["-isa", "?:Type", "?:E", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["isa", "?:Type", "?:E", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],
[
  ["-has type", "?:E", "?:T", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has type", "?:E", "?:T", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],
[
  ["-has actor", "?:E", "?:A", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has actor", "?:E", "?:A", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],
[
  ["-has target", "?:E", "?:T", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has target", "?:E", "?:T", ["$ctxt", "past", "?:W_new", "?:L", "?:K"]]
],

// Special: has time (Explicit Davidsonian Tense Role)
// If E was 'present' in W_old, it is 'past' in the context of W_new.
[
  ["-has time", "?:E", "present", "?:Prep_t", ["$ctxt", "present", "?:W_old", "?:L", "?:K"]],
  ["-before", "?:W_old", "?:W_new"],
  ["has time", "?:E", "past", "?:Prep_t", ["$ctxt", "present", "?:W_new", "?:L", "?:K"]]
],

// experimental
/*
 [["-isa","head","?:Y"],
  ["-has part","?:X","?:Y","?:C"],
  ["is rel2","head of","?:Y","?:X","?:C"]
 ],
 
 [["-isa","head","?:Y"],
  ["-is rel2","head of","?:Y","?:X","?:C"]
 ],
 
 [["has part","?:X","?:Y","?:C"],
  ["-is rel2","head of","?:Y","?:X","?:C"]
 ]
*/


// == 13. TEMPORAL-WORLD INTEGRATION & FUNCTIONAL EXTRACTORS ==

// --- A. $get_world "Destructor" ---
// This makes the function usable by allowing the prover to unify the 
// second element of a context term with a variable.
[ ["=", "?:W", ["$get_world", ["$ctxt", "?:T", "?:W", "?:L", "?:K"]]] ],

// --- B. $theof1/datetime Year to Semantic Tense Bridge ---
// When a world's time (via $theof1) is a $datetime value less than current year,
// infer the world is in the past.
[
  ["-=", ["$theof1", "time", "?:W", "?:C"], ["$datetime", "?:T"]],
  ["-$less", "?:T", 2026],
  ["is_past_world", "?:W"]
],

// --- D. Context Tense Normalization (datetime-triggered only) ---
// When is_past_world(W) holds (currently only via explicit $datetime < 2026),
// rewrite any-tense facts at W to past tense. Does NOT handle the common case
// of LLM tense mismatch (present vs past on the same world without $datetime).
[
  ["-is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["is rel2", "?:R", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],

// Repeat D for other core predicates to ensure universal tense matching
[
  ["-has actor", "?:E", "?:A", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has actor", "?:E", "?:A", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has type", "?:E", "?:V", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has type", "?:E", "?:V", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has target", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has target", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has location", "?:E", "?:P", "?:Prep", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has location", "?:E", "?:P", "?:Prep", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has time", "?:E", "?:T2", "?:Prep", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has time", "?:E", "?:T2", "?:Prep", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has property", "?:P", "?:X", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has property", "?:P", "?:X", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has degree property", "?:P", "?:X", "?:D", "?:R", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has degree property", "?:P", "?:X", "?:D", "?:R", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-have", "?:X", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["have", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has part", "?:X", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has part", "?:X", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has degree rel2", "?:R", "?:X", "?:Y", "?:D", "?:RC", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has destination", "?:E", "?:Y", "?:Prep", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has destination", "?:E", "?:Y", "?:Prep", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has recipient", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has recipient", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has source", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has source", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has beneficiary", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has beneficiary", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has accompaniment", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has accompaniment", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has path", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has path", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has result", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has result", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has topic", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has topic", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],
[
  ["-has cause", "?:E", "?:Y", ["$ctxt", "?:AnyTense", "?:W", "?:L", "?:K"]],
  ["-is_past_world", "?:W"],
  ["has cause", "?:E", "?:Y", ["$ctxt", "past", "?:W", "?:L", "?:K"]]
],

// experimentally defining the comparison between measures

[
  ["-=", "?:M1", ["$list", "?:N1", "?:U"]],
  ["-=", "?:M2", ["$list", "?:N2", "?:U"]],
  ["-$less", "?:N1", "?:N2"],
  ["less_measure", "?:M1", "?:M2"]
],

[
  ["-less_measure", "?:M1", "?:M2"],
  ["-=", "?:M1", ["$list", "?:N1", "?:U"]],
  ["-=", "?:M2", ["$list", "?:N2", "?:U"]],
  ["$less", "?:N1", "?:N2"]
],

[
  ["-$less", "?:N1", "?:N2"],
  ["less_measure", ["$list", "?:N1", "?:U"], ["$list", "?:N2", "?:U"]]
],

[
  ["-less_measure", ["$list", "?:N1", "?:U"], ["$list", "?:N2", "?:U"]],
  ["$less", "?:N1", "?:N2"]
]

]
