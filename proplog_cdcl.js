/*
  CDCL (conflict-driven clause learning) solver for propositional logic,
  easy to hack and experiment with.

  Use like this: proplog_cdcl.cdcl([[-1,2],[1],[-2]])

  Optional arguments and other details below, before exports.cdcl=...
  Fully self-contained, no dependencies.
  Exports function cdcl.

  See http://logictools.org and http://github.com/tammet/logictools
  for UI and other tools.

  This solver is a direct extension of the "dpll: better" solver in
  proplog_dpll.js: the clause representation and the two-watched-literals
  machinery are taken from there, while the recursive search is replaced by the
  conflict-driven clause learning loop. Reading proplog_dpll.js first is
  recommended.

  For CDCL (conflict-driven clause learning) see
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning

  For DPLL (Davis-Putnam-Logemann-Loveland) see
  http://en.wikipedia.org/wiki/DPLL_algorithm

  For a readable description of all the techniques used here see the minisat
  paper "An Extensible SAT-solver" by N. Een and N. Sorensson at
  http://minisat.se/downloads/MiniSat.pdf

  For a modern, high-performance implementation of the same core algorithm see
  https://github.com/arminbiere/kissat

  Recommended to use with the accompanying proplog.html file providing
  a basic user interface and other tools for propositional logic.

  This software is covered by the MIT licence, see http://opensource.org/licenses/MIT
  or http://en.wikipedia.org/wiki/MIT_License

  Copyright (c) 2026 Tanel Tammet (tanel.tammet at gmail.com)
*/



(function(exports) {
  "use strict";

// ====== module start =========

// ------ trace text and the resulting model ------

var trace_flag=false; // false if no trace
var trace_method="text"; // ok values: text, html or console
var trace_list=[];  // list of strings
var origvars=[]; // original variable names to use in trace, if available and not false
var result_model=[]; // set by solver to a resulting model: values of vars

// ------ statistical counts ------

var conflicts_count=0;     // nr of conflicts found, i.e. clauses becoming false
var decisions_count=0;     // nr of variables assigned by a decision, not by propagation
var propagations_count=0;  // nr of assigned literals taken from the propagation queue
var learned_count=0;       // nr of clauses learned from conflicts
var restarts_count=0;      // nr of restarts performed
var reductions_count=0;    // nr of times the learned clauses were thrown away
var max_level_count=0;     // the deepest decision level reached
var units_derived_count=0; // nr of units derived at decision level 0, i.e. plain facts

// ------ constants tuning the search ------

var ACTIVITY_DECAY=0.95;  // how fast the activity of an old conflict fades away
var ACTIVITY_LIMIT=1e100; // activities are rescaled before they overflow to Infinity
var RESTART_BASE=128;     // the shortest restart interval, in conflicts
var LEARNED_FACTOR=0.4;   // learned clauses allowed, as a fraction of the input clauses
var LEARNED_MINIMUM=500;  // ... but always at least this many
var LEARNED_GROWTH=1.1;   // the allowed number grows by this factor after each reduction

// ------ the state of the search ------
//
// Unlike proplog_dpll.js, which passes the state around as function arguments
// (a leftover of its recursive search), we keep the state in module-level
// variables: this keeps the iterative main loop below readable. All of them are
// created and initialized in exports.cdcl, hence repeated calls are independent.

var varvals;       // Int32Array: 0 if unassigned, 1 if assigned true, -1 if assigned false
var varlevel;      // Int32Array: the decision level at which the variable was assigned
var varreason;     // Array: the clause which forced the value, 0 for decisions and facts
var varactivities; // Array: activity of a variable, larger is preferred for the next decision
var savedphase;    // Int32Array: the value a variable had when it was last unassigned
var seen;          // Int32Array: scratch flags of conflict analysis, all zero between analyses
var posbuckets;    // Array of arrays: clauses watching a positive literal, see makebuckets
var negbuckets;    // Array of arrays: clauses watching a negative literal, see makebuckets
var trail;         // Int32Array: assigned literals in the order they were assigned
var trailend;      // nr of literals actually stored in the trail
var qhead;         // index of the next trail literal waiting to be propagated
var levelstarts;   // Array: levelstarts[l] is the trail index where decision level l starts
var decisionlevel; // the number of decisions currently present on the trail
var activity_inc;  // the amount added to the activity of a variable when it is bumped
var origclauses;   // Array: the clauses given to the solver, without the learned ones
var learnedclauses;// Array: the clauses learned from conflicts, in the order learned
var max_learned;   // when the learned clauses grow over this many, half are thrown away
var reduce_pending;// true if the learned clauses should be thrown away at the next chance

// ====== cdcl solver ==========

/*
  Check whether a clause set is satisfiable, using an implementation of the
  cdcl (conflict-driven clause learning) procedure.

  CDCL keeps everything the dpll procedure does - assigning variables one by one
  and deriving the consequences by unit propagation - and adds the crucial ability
  to *learn from its mistakes*:

  - The assignments are kept in one long array called the trail, in the order they
    were made, instead of being kept implicitly in the recursion stack of a
    recursive search function. The search is thus a plain loop, not a recursion.
  - Each variable assigned by unit propagation remembers the clause which forced
    its value: this clause is called the *reason* of the variable. Decisions -
    variables we simply guessed a value for - have no reason. Reasons turn the
    trail into an implication graph: they say why each value had to be what it is.
  - When a clause becomes false (a *conflict*) we do not simply backtrack and try
    the opposite value like dpll does. Instead we walk the implication graph
    backwards from the conflict, resolving the false clause with the reasons of
    the variables involved, until we obtain a clause describing a *cause* of the
    conflict: see the analyze function below. This new clause is *learned*, i.e.
    added to the clause set, and it guarantees that the same conflict is never
    encountered again anywhere in the rest of the search.
  - The learned clause also tells us how far back to jump: all its literals except
    one are false at earlier decision levels, so we jump straight back to the
    deepest of these levels - possibly many levels at once - where the learned
    clause immediately forces the value of its one remaining literal. This is
    called *backjumping* or non-chronological backtracking.

  Two more things are needed to make all this actually pay off:

  - learned clause minimization: a literal of a freshly learned clause is dropped
    if the other literals of the clause already imply it, see minimize_learned.
  - learned clause deletion: a clause is learned from every single conflict, so
    without regularly throwing the less useful ones away the clause set grows
    until propagation crawls, see reduce_learned.

  On top of that the solver uses three standard heuristics:

  - activities in the style of VSIDS (variable state independent decaying sum):
    variables taking part in recent conflicts get their activity bumped and are
    preferred when choosing the next variable to assign.
  - phase saving: a variable is first tried with the value it had when it was
    last unassigned by backjumping.
  - restarts following the Luby sequence: the search is regularly thrown back to
    decision level 0, keeping all the learned clauses, activities and saved phases.
    A restart costs almost nothing and cures unlucky early decisions.

  The clause set is unsatisfiable iff a conflict occurs when no decisions have been
  made, i.e. at decision level 0: then the conflict follows from the clause set
  alone. It is satisfiable iff all the variables get a value without a conflict.

  Inherited from proplog_dpll.js and not explained here again:
  - clauses are organized into buckets for all the literals: a clause is in the
    bucket of a literal iff this literal is one of the two literals watched
  - two watched literals per clause: a clause is looked at during propagation only
    when one of its two watched literals becomes false

  Added here on top of that: simple preprocessing before the search starts, doing
  limited unit propagation/subsumption, tautology deletion and duplicate literal
  deletion. Notice that this is only safe because the units it finds are
  propagated through the whole clause set before the first decision is made:
  see the comment at the propagation of the preprocessing units below.

  Deliberately not implemented, to keep the code readable - good starting points
  for experimenting, see the minisat paper and kissat:
  - a priority queue for choosing the next variable, instead of scanning them all
  - the recursive version of learned clause minimization, removing more literals
  - measuring the quality of a learned clause by its "literal block distance"
    instead of its length, when choosing the clauses to throw away
  - inprocessing: variable elimination, subsumption, vivification during the search

  A word of warning about what to expect. On the randomly generated 3-sat problems
  of our problem generator this solver and the plain "dpll: better" are roughly on
  par: uniform random problems have no structure for the learned clauses to catch,
  and both solvers have a long tail of unlucky instances. Clause learning wins on
  problems with structure - which is what the problems coming from real
  applications look like - and this is why all the modern high-performance solvers
  are built on cdcl.

  Take
    clauses: a clause set (array of integer arrays) like [[1,-2],[-2,1]]
    maxvarnr: (optional) the maximal variable in clauses (integer) like 2.
    trace: (optional) either false,"html","txt" or "console"
      for trace generation and output
    varnames: (optional) an array of variable names used in trace and resulting
      model instead of integers, like [0,"x","y","z1","z2"]

  Return a list of two elements [result,tracetext] where:

    result is false iff the clause set is contradictory (like [[1],[-1]])
    result is a model (list of signed literals) if the clause set has a model

    tracetext is a human-readable string containing either only statistics
      or trace+statistics: the tracetext format depends on the
      passed trace parameter
*/

exports.cdcl = function (clauses,maxvarnr,trace,varnames) {
  var i,tmp,confl,analysis,learned,backlevel,lit;
  var conflicts_until_restart,conflicts_at_last_restart;
  // store trace and origvars to globals
  if (trace) { trace_flag=true; trace_method=trace; }
  else { trace_flag=false; }
  if (varnames) origvars=varnames;
  else origvars=false;
  // zero statistics and trace globals
  conflicts_count=0;
  decisions_count=0;
  propagations_count=0;
  learned_count=0;
  restarts_count=0;
  reductions_count=0;
  max_level_count=0;
  units_derived_count=0;
  trace_list=[];
  result_model=[];
  // First add two meta-info els to the beginning of each clause:
  // the two meta-elements are later used for clause signature during
  // simplification and as watched literal pointers during search.
  // Also, get the nr of the largest variable in the clause set.
  tmp=maxvar_and_meta(clauses);
  maxvarnr=tmp[0];
  clauses=tmp[1];
  // create and initialize the arrays used during search
  varvals=new Int32Array(maxvarnr+1);
  varlevel=new Int32Array(maxvarnr+1);
  varreason=new Array(maxvarnr+1);
  savedphase=new Int32Array(maxvarnr+1);
  seen=new Int32Array(maxvarnr+1);
  varactivities=new Array(maxvarnr+1);
  trail=new Int32Array(maxvarnr+1); // at most one literal per variable
  posbuckets=new Array(maxvarnr+1);
  negbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) {
    varvals[i]=0;
    varlevel[i]=0;
    varreason[i]=0;
    savedphase[i]=1; // a variable never yet assigned is first tried as true
    seen[i]=0;
    varactivities[i]=0;
    posbuckets[i]=[];
    negbuckets[i]=[];
  }
  activity_inc=1;
  trailend=0;
  qhead=0;
  decisionlevel=0;
  levelstarts=[0]; // decision level 0 starts at the very beginning of the trail

  // ------ preprocessing: may be omitted, the search does not depend on it ------

  clauses=simplify_clause_list(clauses);
  if (clauses===false) { // an empty clause was found: nothing left to search for
    if (trace_flag) print_trace(0,"contradiction found during preprocessing");
    trace_list.push(statistics_str("preprocessing finished"));
    return [false,trace_list.join("\r\n")];
  }
  initial_activities(clauses); // occurrence counts give the first decisions a direction
  makebuckets(clauses); // start watching the first two literals of each clause
  origclauses=clauses;
  learnedclauses=[];
  reduce_pending=false;
  max_learned=Math.floor(clauses.length*LEARNED_FACTOR);
  if (max_learned<LEARNED_MINIMUM) max_learned=LEARNED_MINIMUM;

  // The units detected during preprocessing become the first elements of the
  // trail: they are facts holding at decision level 0 and have no reason clause.
  // Propagating them before the first decision is made is not just an
  // optimization, it is what makes the preprocessing above safe: the units are
  // derived in a single pass over the clause list, hence a unit derived late in
  // the pass may well falsify a clause the pass has already passed over. The
  // propagation below looks at all such clauses and finds any contradiction.
  for(i=1;i<=maxvarnr;i++) {
    if (varvals[i]!==0) {
      trail[trailend]=i*varvals[i];
      trailend++;
      varlevel[i]=0;
      varreason[i]=0;
    }
  }

  // ------ the main cdcl loop ------

  conflicts_until_restart=RESTART_BASE*luby(restarts_count);
  conflicts_at_last_restart=0;
  while(true) {
    // derive everything derivable from the current assignments
    confl=propagate();
    if (confl!==0) {
      // ---- a clause became false: learn from the conflict and jump back ----
      conflicts_count++;
      if (decisionlevel===0) {
        // nothing was guessed, hence the clause set itself is contradictory
        if (trace_flag) print_trace(0,"conflict without any decisions made");
        trace_list.push(statistics_str("search finished"));
        return [false,trace_list.join("\r\n")];
      }
      analysis=analyze(confl);
      learned=analysis[0];  // literals of the new clause, asserting literal first
      backlevel=analysis[1]; // the decision level to jump back to
      if (trace_flag) {
        print_trace(decisionlevel,"learned clause: "+lit_list_to_str(learned)+
                                  "and backjumping to level "+backlevel);
      }
      backjump(backlevel);
      install_learned(learned);
      decay_activities();
      if (learnedclauses.length>=max_learned) {
        // ---- too many learned clauses: go back to the start and throw half away ----
        // The actual throwing away is done in the other branch below, where
        // everything derivable at decision level 0 has just been derived.
        reduce_pending=true;
        backjump(0);
      } else if (conflicts_count-conflicts_at_last_restart>=conflicts_until_restart) {
        // ---- enough conflicts have accumulated: restart the search ----
        restarts_count++;
        conflicts_at_last_restart=conflicts_count;
        conflicts_until_restart=RESTART_BASE*luby(restarts_count);
        if (trace_flag) {
          print_trace(0,"restart nr "+restarts_count+", next restart after "+
                        conflicts_until_restart+" conflicts");
        }
        backjump(0);
      }
    } else {
      // ---- no conflict: guess a value for one more variable ----
      if (reduce_pending && decisionlevel===0) {
        reduce_learned();
        reduce_pending=false;
      }
      lit=next_decision();
      if (lit===0) {
        // all the variables have a value and no clause is false: we have a model
        store_model(varvals);
        trace_list.push(statistics_str("search finished"));
        return [result_model,trace_list.join("\r\n")];
      }
      decisionlevel++;
      levelstarts.push(trailend); // the new level starts here, before the decision
      if (decisionlevel>max_level_count) max_level_count=decisionlevel;
      if (trace_flag) print_trace(decisionlevel,"deciding "+showvar(lit));
      enqueue(lit,0); // a decision has no reason clause
    }
  }
}

// ================= unit propagation ========================

/* Assign all the values forced by the assignments waiting in the trail.

  Take the next unpropagated literal from the trail and look at all the clauses
  watching the opposite - now false - literal. Such a clause can be in one of
  four states:

  - the other watched literal is true: the clause is satisfied, nothing to do.
  - the clause contains some other literal which is not false: start watching
    that one instead of the falsified literal and move the clause to the bucket
    of the new watched literal. This is the whole point of watching two literals:
    a clause is looked at only when one of its two watched literals becomes false,
    and a long clause with many unassigned literals is almost never looked at.
  - no replacement found and the other watched literal is unassigned: the clause
    has become a unit clause forcing the value of that literal. Assign it and
    remember the clause as the reason of the assignment.
  - no replacement found and the other watched literal is false as well: all the
    literals of the clause are false, i.e. we have a conflict.

  Returns the conflicting clause, or 0 if no conflict was found. Note that unlike
  the unit propagation of proplog_dpll.js this function does not undo anything on
  a conflict: the whole trail is needed for analyzing the conflict, and only
  backjump undoes assignments.
*/

function propagate() {
  var dlit,negdlit,bucket,bucketlen,i,j,clause,otherw,lit,nr,polarity,found;
  while(qhead<trailend) {
    dlit=trail[qhead]; // the literal to propagate: it is true
    qhead++;
    propagations_count++;
    negdlit=0-dlit; // this literal is false now, look at the clauses watching it
    if (dlit<0) bucket=posbuckets[negdlit];
    else bucket=negbuckets[dlit];
    bucketlen=bucket[0]; // nr of used bucket elements: the array is normally longer
    for(i=1;i<=bucketlen;i++) { // iterate over the clauses in the bucket
      clause=bucket[i];
      // the other watched literal is the one in the meta-slot not holding negdlit
      if (clause[0]===negdlit) otherw=clause[1];
      else otherw=clause[0];
      // if the other watched literal is true, the clause is satisfied
      if (otherw<0) {nr=0-otherw; polarity=-1}
      else {nr=otherw; polarity=1};
      if (varvals[nr]===polarity) continue;
      // look for a literal to watch instead of the falsified negdlit:
      // any literal which is not false and is not the other watched literal
      found=0;
      for(j=2;j<clause.length;j++) {
        lit=clause[j];
        if (lit===otherw) continue;
        if (lit<0) {nr=0-lit; polarity=-1}
        else {nr=lit; polarity=1};
        if (varvals[nr]!==(0-polarity)) { found=lit; break; } // not false: watch this
      }
      if (found!==0) {
        // move the watch from negdlit to the found literal
        if (clause[0]===negdlit) clause[0]=found;
        else clause[1]=found;
        addwatch(found,clause);
        // remove the clause from the current bucket:
        // move the last used el of the bucket to the current position
        bucket[i]=bucket[bucketlen];
        bucket[0]--;
        bucketlen--;
        i--; // the clause moved to the current position must be looked at as well
        continue;
      }
      // no replacement found: all the literals except otherw are false
      if (otherw<0) {nr=0-otherw; polarity=-1}
      else {nr=otherw; polarity=1};
      if (varvals[nr]===(0-polarity)) {
        // otherw is false too, hence the whole clause is false
        if (trace_flag) print_trace(decisionlevel,"conflict in clause: "+clause_to_str(clause));
        return clause;
      }
      // otherw is unassigned: the clause forces it to be true
      enqueue(otherw,clause);
      if (trace_flag) {
        print_trace(decisionlevel,"derived "+showvar(otherw)+
                                  " from clause: "+clause_to_str(clause));
      }
    }
    // bucket loop ended
  }
  return 0; // no conflict found
}

/* Assign a literal to true and push it to the end of the trail.

  The reason is the clause which forced this value, or 0 for a decision or a
  fact derived at decision level 0. The caller guarantees that the variable of
  the literal is currently unassigned.
*/

function enqueue(lit,reason) {
  var nr;
  if (lit<0) {nr=0-lit; varvals[nr]=-1}
  else {nr=lit; varvals[nr]=1};
  varlevel[nr]=decisionlevel;
  varreason[nr]=reason;
  trail[trailend]=lit;
  trailend++;
  // a literal assigned without any decisions made is a plain fact
  if (decisionlevel===0) units_derived_count++;
}

/* Add a clause to the bucket of a literal, i.e. start watching this literal.

  The buckets built by makebuckets contain spare placeholder slots, but learned
  clauses are added later and may need more room, hence the bounds check.
*/

function addwatch(lit,clause) {
  var bucket;
  if (lit<0) bucket=negbuckets[0-lit];
  else bucket=posbuckets[lit];
  bucket[0]++;
  if (bucket[0]>=bucket.length) bucket.push(clause); // no spare slot left
  else bucket[bucket[0]]=clause;
}

// ================= making decisions ========================

/* Find the next unassigned variable to assign and the value to try first.

  The variable with the largest activity is selected: activities are bumped
  during conflict analysis, hence we prefer the variables which took part in
  the recent conflicts. The value tried first is the value the variable had
  when it was last unassigned (phase saving); a variable never yet assigned
  is tried as true.

  Returns the literal to assign, or 0 if all the variables are assigned.
  Real solvers keep the variables in a priority queue instead of scanning
  them all: the scan is easier to read and fast enough here.
*/

function next_decision() {
  var i,activity,bestfound,maxactivity;
  maxactivity=-1;
  bestfound=0;
  for(i=1;i<varvals.length;i++) {
    if (varvals[i]!==0) continue;
    activity=varactivities[i];
    if (activity>=maxactivity) {
      maxactivity=activity;
      bestfound=i;
    }
  }
  if (bestfound===0) return 0; // no unassigned variables left
  decisions_count++;
  return bestfound*savedphase[bestfound];
}

// ================= learning from a conflict ========================

/* Analyze a conflict and build a new clause to be learned from it.

  We are given a clause all the literals of which are false. Some of them were
  assigned at earlier decision levels, at least one at the current level. Each
  literal assigned by propagation has a reason clause: resolving the conflicting
  clause with the reason of one of its literals removes that literal and brings
  in the literals which caused it. Doing this repeatedly, always taking the
  literal assigned last, we eventually reach a clause containing exactly one
  literal of the current decision level: this literal is the *first unique
  implication point* (1UIP), a single assignment of the current level through
  which all the paths from the decision to the conflict pass.

  Every clause obtained this way is a logical consequence of the clause set,
  hence adding it to the clause set is safe. It is also useful: all its literals
  are false right now, so after backjumping it immediately forces the opposite
  value of the 1UIP literal, and it blocks the same conflict forever after.

  A worked example. Clauses (among others): [-2,3], [-3,-1,4], [-3,-4].
  We decide 1 at level 1 and 2 at level 2. Propagation at level 2 derives:
      3 from [-2,3]        (reason of 3)
      4 from [-3,-1,4]     (reason of 4)
  and then [-3,-4] has both literals false: a conflict. Analysis starts from the
  conflicting clause [-3,-4] whose literals -3 and -4 are both of the current
  level, so two of them are still to be resolved away. The literal assigned last
  is 4, so we resolve with its reason [-3,-1,4]:
      [-3,-4] + [-3,-1,4]  gives  [-3,-1]
  Now -1 is of level 1 and stays in the clause, while -3 is the only literal of
  the current level left: 3 is the 1UIP and [-3,-1] is the learned clause. Its
  deepest literal apart from -3 is -1 of level 1, so we jump back to level 1,
  undoing the decision 2 and everything derived from it. There the learned clause
  [-3,-1] is a unit clause forcing -3: we have learned that 1 implies -3 and the
  search continues from a strictly better position than where it started.

  Two details worth noticing in the code below:
  - the literal we resolve upon is skipped when the reason clause is scanned:
    it is exactly the literal which disappears in the resolution step.
  - literals assigned at level 0 are skipped altogether: they are false no matter
    what we decide later, hence they would be dead weight in the learned clause.

  Returns a list of two elements [lits,backlevel] where
    lits is an array of the literals of the learned clause: lits[0] is the
      asserting literal (the negated 1UIP) and, if the clause is longer than one
      literal, lits[1] is a literal of the deepest remaining level. These two
      become the watched literals of the learned clause.
    backlevel is the decision level to jump back to.
*/

function analyze(confl) {
  var lits,minimized,counter,lit,litvar,index,c,j,q,v,k,best,backlevel;
  lits=[0];         // slot 0 is reserved for the asserting literal found at the end
  counter=0;        // nr of the current level literals not yet resolved away
  lit=0;            // the literal resolved upon, none for the conflicting clause
  litvar=0;         // and its variable
  index=trailend-1; // where to look for the next literal to resolve upon
  c=confl;          // the clause to take literals from
  do {
    for(j=2;j<c.length;j++) {
      q=c[j];
      if (q<0) v=0-q; else v=q;
      if (v===litvar) continue;      // the literal resolved upon disappears
      if (seen[v]!==0) continue;     // already counted or already in the clause
      if (varlevel[v]===0) continue; // false at level 0, hence false forever
      seen[v]=1;
      bump_activity(v);
      if (varlevel[v]===decisionlevel) counter++; // to be resolved away later
      else lits.push(q); // an earlier level: this literal stays in the learned clause
    }
    // the next literal to resolve upon is the one assigned last among the
    // current level literals collected: scan the trail backwards to find it
    while(true) {
      lit=trail[index];
      index--;
      if (lit<0) litvar=0-lit; else litvar=lit;
      if (seen[litvar]!==0) break;
    }
    seen[litvar]=0;
    counter--;
    c=varreason[litvar]; // resolve with the reason of this literal
  } while(counter>0);
  // exactly one literal of the current decision level is left: the 1UIP.
  // Negating it gives the asserting literal of the learned clause.
  lits[0]=0-lit;
  // shorten the clause before using it: see minimize_learned below
  seen[absvar(lits[0])]=1; // the asserting literal is in the clause as well
  minimized=minimize_learned(lits);
  // clear the seen flags: they must be all zero for the next analysis.
  // Note that this uses the unminimized list, since a flag was set for each of
  // its literals, also for the ones just removed.
  for(k=0;k<lits.length;k++) seen[absvar(lits[k])]=0;
  lits=minimized;
  // find the deepest level among the other literals: this is the level where
  // the learned clause becomes a unit clause, hence the level to jump back to
  if (lits.length===1) {
    backlevel=0; // a learned unit clause is a fact holding at level 0
  } else {
    best=1;
    for(k=2;k<lits.length;k++) {
      if (varlevel[absvar(lits[k])]>varlevel[absvar(lits[best])]) best=k;
    }
    q=lits[1]; lits[1]=lits[best]; lits[best]=q; // to slot 1: it becomes watched
    backlevel=varlevel[absvar(lits[1])];
  }
  return [lits,backlevel];
}

/* Remove the literals of a learned clause which the other literals already imply.

  Suppose a literal q of the learned clause was assigned by propagation, and every
  literal of the reason clause of q is either in the learned clause already or
  false at decision level 0. Resolving the learned clause with that reason then
  simply removes q and adds nothing new, so the clause without q is a logical
  consequence just as well - and a shorter clause forbids more and propagates more
  often. This is called self-subsuming resolution or learned clause minimization
  and it typically removes a good part of the literals almost for free.

  The seen flags of all the literals of the learned clause are still set when this
  is called, which makes "is this literal in the learned clause" a single lookup.

  Only one round of removals is done here, looking at the immediate reasons.
  Minisat also has a recursive version, which looks further back and removes more.
*/

function minimize_learned(lits) {
  var out,k,j,v,q,reason,redundant;
  out=[lits[0]]; // the asserting literal is what the clause is for: it always stays
  for(k=1;k<lits.length;k++) {
    v=absvar(lits[k]);
    reason=varreason[v];
    if (reason===0) { out.push(lits[k]); continue; } // a decision, nothing implies it
    redundant=true;
    for(j=2;j<reason.length;j++) {
      q=absvar(reason[j]);
      if (q===v) continue; // the literal itself: it is what the resolution removes
      if (seen[q]===0 && varlevel[q]>0) { redundant=false; break; }
    }
    if (!redundant) out.push(lits[k]);
  }
  return out;
}

/* Undo all the assignments made after the given decision level.

  Unassigning a variable saves its current value as the phase to try first when
  the variable is decided upon again. Nothing else is undone: the learned clauses,
  the activities and the saved phases are all kept, and they are the reason why
  the search does not simply repeat itself after a backjump.
*/

function backjump(level) {
  var k,lit,nr,firstundone;
  if (level>=decisionlevel) return; // nothing to undo
  firstundone=levelstarts[level+1]; // the trail position where the next level starts
  for(k=trailend-1;k>=firstundone;k--) {
    lit=trail[k];
    if (lit<0) nr=0-lit; else nr=lit;
    savedphase[nr]=varvals[nr]; // remember the value for the next time
    varvals[nr]=0;
    varreason[nr]=0;
  }
  trailend=firstundone;
  qhead=trailend; // everything left on the trail has already been propagated
  levelstarts.length=level+1;
  decisionlevel=level;
}

/* Add a learned clause to the clause set and assign its asserting literal.

  The clause is built in exactly the same format as the input clauses: two
  meta-slots holding the watched literals, then the literals themselves.
  The two literals watched are lits[0] and lits[1] as prepared by analyze:
  the asserting literal and a literal of the level we just jumped back to.
  These two are the last literals of the clause to become false again after
  any later backjump, which is exactly what the watching scheme requires.

  All the literals of the clause except the asserting one are false right now,
  hence the clause forces the asserting literal to be true. Learned clauses are
  never deleted here: real solvers periodically throw the useless ones away.
*/

function install_learned(lits) {
  var i,clause;
  learned_count++;
  if (lits.length===1) {
    // a learned unit clause is a fact: we have jumped back to level 0
    enqueue(lits[0],0);
    return;
  }
  clause=new Int32Array(lits.length+2);
  clause[0]=lits[0]; // first watched literal
  clause[1]=lits[1]; // second watched literal
  for(i=0;i<lits.length;i++) clause[i+2]=lits[i];
  addwatch(lits[0],clause);
  addwatch(lits[1],clause);
  learnedclauses.push(clause);
  enqueue(lits[0],clause);
}

/* Throw away the less useful half of the learned clauses.

  Learning a clause from every single conflict means the clause set keeps growing,
  and propagation - which has to look at every clause watching a falsified literal
  - keeps getting slower and slower. Without this function the solver would end up
  losing to the plain dpll solver on larger problems. Real solvers therefore
  regularly delete the learned clauses which do not seem to pull their weight.

  The criterion used here is the simplest useful one: the shorter a clause, the
  more assignments it forbids and the more often it takes part in propagation,
  hence we keep the shorter half. Modern solvers use the better "literal block
  distance" instead: the number of different decision levels of the literals of a
  clause, smaller being better.

  Deleting clauses is safe here because this is only done when no decisions have
  been made and everything derivable at decision level 0 has been derived: no
  clause is then needed as the reason of an assignment - conflict analysis never
  looks at the reasons of the level 0 assignments - and the watched literals of
  the clauses left can simply be chosen anew.
*/

function reduce_learned() {
  var i,keep;
  reductions_count++;
  learnedclauses.sort(function(a,b){return a.length-b.length});
  keep=Math.floor(learnedclauses.length/2);
  learnedclauses.length=keep;
  // all the watched literals are chosen anew, hence start with empty buckets
  for(i=1;i<varvals.length;i++) {
    posbuckets[i]=[0];
    negbuckets[i]=[0];
  }
  for(i=0;i<origclauses.length;i++) watch_clause(origclauses[i]);
  for(i=0;i<learnedclauses.length;i++) watch_clause(learnedclauses[i]);
  // give the search more room before the next reduction
  max_learned=Math.floor(max_learned*LEARNED_GROWTH);
  if (trace_flag) {
    print_trace(0,"learned clauses cut down to "+keep+
                  ", next reduction at "+max_learned);
  }
}

/* Choose the two literals to watch in a clause, at decision level 0.

  A clause containing a literal which is true at decision level 0 is satisfied no
  matter what happens later: such a clause is simply left out of the watch lists.
  Any other clause has at least two unassigned literals - a clause with fewer
  would already have been used for propagation or would have been a conflict -
  and the first two of these are watched.
*/

function watch_clause(clause) {
  var j,lit,nr,polarity,first,second;
  first=0;
  second=0;
  for(j=2;j<clause.length;j++) {
    lit=clause[j];
    if (lit<0) {nr=0-lit; polarity=-1}
    else {nr=lit; polarity=1};
    if (varvals[nr]===polarity) return; // true at level 0: satisfied forever
    if (varvals[nr]===0) { // unassigned: a good literal to watch
      if (first===0) first=lit;
      else if (second===0) second=lit;
    }
  }
  if (second===0) {
    // cannot happen as explained above, but if it ever did, watching the first
    // two literals of the clause keeps the clause in the search in any case
    first=clause[2];
    second=clause[3];
  }
  clause[0]=first;
  clause[1]=second;
  addwatch(first,clause);
  addwatch(second,clause);
}

// ================= activities and restarts ========================

/* Increase the activity of a variable taking part in the current conflict.

  Instead of multiplying all the old activities by ACTIVITY_DECAY after each
  conflict, we increase the amount added to the activity - the effect on the
  relative order of the variables is the same, but it takes constant time.
  Activities grow exponentially this way, so they are rescaled before they
  would overflow to Infinity.
*/

function bump_activity(v) {
  var i;
  varactivities[v]+=activity_inc;
  if (varactivities[v]>ACTIVITY_LIMIT) {
    for(i=1;i<varactivities.length;i++) varactivities[i]=varactivities[i]/ACTIVITY_LIMIT;
    activity_inc=activity_inc/ACTIVITY_LIMIT;
  }
}

function decay_activities() {
  activity_inc=activity_inc/ACTIVITY_DECAY;
}

/* The x-th element (counting from 0) of the Luby sequence
   1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...

  The restart interval is RESTART_BASE times this number of conflicts: most
  restarts come quickly one after another, but the intervals in between grow
  without a limit, so the solver both retries often and is still able to finish
  a long search. This schedule is provably close to optimal for randomized
  algorithms with an unknown runtime distribution, see M. Luby, A. Sinclair,
  D. Zuckerman, "Optimal speedup of Las Vegas algorithms" (1993).
*/

function luby(x) {
  var size,seq;
  // find the smallest full binary subsequence of length size=2^k-1 containing x
  for(size=1,seq=0; size<x+1; seq++,size=2*size+1) {}
  // and descend into it until x is the last element of the subsequence found
  while(size-1!==x) {
    size=(size-1)>>1;
    seq--;
    x=x%size;
  }
  return Math.pow(2,seq);
}

// ================= preprocessing phase ========================

/* Adds two extra meta-info elements to the beginning of each clause,
   returning a new clause set with the augmented clauses.

   The two meta-elements are used for the clause signature during
   simplification and as watched literal pointers during search.
   Example:  [3,-1] becomes [0,0,3,-1],  [4] becomes [0,0,4]

   Additionally, find the largest variable number.
   Returns a list:
   [max_var_nr_found, new_clause_list]
*/

function maxvar_and_meta(clauses) {
  var i,j,c,nc,clen,lit,nr,maxvarnr,clauses2;
  maxvarnr=0;
  clauses2=[];
  for (i=0;i<clauses.length;i++) {
    c=clauses[i];
    clen=c.length;
    nc=new Int32Array(clen+2);
    nc[0]=0;
    nc[1]=0;
    for(j=0;j<clen;j++) {
      lit=c[j];
      nc[j+2]=lit;
      if (lit<0) nr=0-lit;
      else nr=lit;
      if (nr>maxvarnr) maxvarnr=nr;
    }
    clauses2.push(nc);
  }
  return [maxvarnr,clauses2];
}

/* Optional clause list simplification:
   - unit resolution and subsumption
   - tautology elimination
   - duplicate literals elimination

   The clauses are sorted by length, hence the unit clauses are looked at first
   and their values are used for cutting the longer clauses. The values found
   are stored to varvals and become the level 0 part of the trail.

   Returns the simplified clause list, or false if a contradiction was found.
   All the clauses of the returned list have at least two literals.
*/

function simplify_clause_list(clauses) {
  var clauses2,i,j,k,clause,lit,nlit,nr,sign,remove,cuts,dups,nlen,nc,s;
  clauses=clauses.sort(function(a,b){return a.length-b.length});
  // loop over clauses to remove tautologies and duplicate literals
  // and to perform unit subsumption and cutoff
  clauses2=[];
  for(i=0;i<clauses.length;i++) {
    clause=clauses[i];
    remove=false;
    cuts=0;
    dups=0;
    for(j=2;j<clause.length;j++) {
      lit=clause[j];
      nlit=0-lit;
      if (lit<0) {nr=0-lit; sign=-1; }
      else {nr=lit; sign=1; }
      if (varvals[nr]===sign) { remove=true; break; } // subsumed by a unit clause
      if (varvals[nr]===0-sign) { clause[j]=0; cuts++; continue; } // cut off by a unit
      for(k=2;k<j;k++) { // check for tautology and duplicate literals
        if(clause[k]===nlit) { remove=true; break; }
        if(clause[k]===lit) { clause[j]=0; dups++; }
      }
      if (remove) break; // do not keep tautologies
    }
    if (remove) continue;
    nlen=clause.length-(cuts+dups);
    if (nlen===2) return false; // all the literals were cut off: an empty clause
    if (nlen===3) {
      // a unit clause: store the value of the variable
      units_derived_count++;
      for(k=2;k<clause.length;k++) {
        if (clause[k]!==0) {lit=clause[k]; break; }
      }
      if (lit<0) {nr=0-lit; sign=-1; }
      else {nr=lit; sign=1; }
      varvals[nr]=sign;
      continue;
    }
    if (nlen!==clause.length) {
      // some literals were removed: build a shorter clause
      nc=new Int32Array(nlen);
      nc[0]=clause[0];
      nc[1]=clause[1];
      k=2;
      for(j=2;j<clause.length;j++) {
        if (clause[j]===0) continue;
        nc[k]=clause[j];
        k++;
      }
      clause=nc;
    }
    clauses2.push(clause);
  }
  if (trace_flag) {
    s="units detected or derived during preprocessing: ";
    for(i=1;i<varvals.length;i++) {
      if (varvals[i]!==0) s+=" "+showvar(i*varvals[i]);
    }
    print_trace(0,s);
  }
  return clauses2;
}

/* Give the variables their initial activities by counting occurrences.

   A variable occurring in many clauses is a good variable to assign early, and
   an occurrence in a short clause counts for more than an occurrence in a long
   one: short clauses are harder to satisfy. These initial activities only direct
   the first decisions: as soon as conflicts start coming in, the activities
   bumped during conflict analysis take over.

   Unlike proplog_dpll.js we do not look for pure literals (variables occurring
   with one polarity only): removing them is not compatible with clause learning,
   since the learned clauses may contain both polarities of any variable.
*/

function initial_activities(clauses) {
  var i,j,clause,nlits,lit,nr,bonus;
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];
    nlits=clause.length-2; // the first two elements are meta-info
    if (nlits<3) bonus=20;
    else if (nlits<4) bonus=15;
    else {
      bonus=10-nlits;
      if (bonus<1) bonus=1;
    }
    for (j=2; j<clause.length; j++) {
      lit=clause[j];
      if (lit<0) nr=0-lit;
      else nr=lit;
      varactivities[nr]+=bonus;
    }
  }
  if (trace_flag) {
    var s="initial variable activities: ";
    for(i=1;i<varactivities.length;i++) s+=showvar(i)+":"+varactivities[i]+" ";
    print_trace(0,s);
  }
}

/* creates the global posbuckets and negbuckets arrays for all vars:
   each bucket is an array of clauses watching the literal, i.e. clauses
   having this literal in one of the two meta-slots.

   The first el is the number of actually used clauses in the bucket.
   Then come used clauses, finally placeholders to be potentially
   filled later by addwatch.

   The two literals watched initially are simply the first two literals of the
   clause: all the clauses have at least two literals after simplification, and
   the values found during preprocessing are propagated before any decision is
   made, which moves the watches away from the literals already false.
*/

function makebuckets(clauses) {
  var i,j,k,clause,lit,bucket;

  for(i=0;i<clauses.length;i++) {
    clause=clauses[i];
    k=0; // nr of watched literals handled: max 2
    for(j=2;j<clause.length;j++) {
      lit=clause[j];
      if(lit<0) bucket=negbuckets[0-lit];
      else bucket=posbuckets[lit];
      if (k<2) {
        clause[k]=lit; // store watched lit to meta-field
        k++;
        // actually store clause to beginning of bucket
        bucket.unshift(clause);
      } else {
        // just append empty placeholder to end of bucket for potential later use
        bucket.push(0);
      }
    }
  }
  // add nr of actually used clauses to beginning of each bucket
  for(i=1;i<negbuckets.length;i++) {
    // negative
    bucket=negbuckets[i];
    for(j=0;j<bucket.length;j++) {
      if (bucket[j]===0) break;
    }
    negbuckets[i].unshift(j);
    // positive
    bucket=posbuckets[i];
    for(j=0;j<bucket.length;j++) {
      if (bucket[j]===0) break;
    }
    posbuckets[i].unshift(j);
  }
  return clauses;
}

// ======== printing the result and the trace ============

/*
  Store the current valuation of variables to be printed out later as a model.
*/

function store_model(varvals) {
  var i;
  for(i=1;i<varvals.length;i++) {
    // store assigned values as -1, 3, -4, ...
    if (varvals[i]!==0) result_model.push(showvar(i*varvals[i]));
  }
}

/*
  The statistics line printed at the end of the search, with or without a trace.
  Comparing these numbers with the numbers printed by the dpll solvers shows
  what clause learning actually buys: far fewer assignments for the same problem.
*/

function statistics_str(prefix) {
  var txt;
  txt=prefix+": conflicts "+conflicts_count;
  txt+=", decisions "+decisions_count;
  txt+=", propagations "+propagations_count;
  txt+=", learned clauses "+learned_count;
  txt+=", restarts "+restarts_count;
  txt+=", learned clause reductions "+reductions_count;
  txt+=", max level "+max_level_count;
  txt+=", level 0 units "+units_derived_count;
  return txt;
}

/* The trace is indented by the current decision level, just like the trace of
   the dpll solvers is indented by the depth of the recursion.
*/

function print_trace(depth,txt) {
  var i,s="";
  if (trace_flag && trace_method=="console") {
    for(i=0;i<depth;i++) s+=" ";
    console.log(s+txt);
  } else if (trace_flag && trace_method=="text") {
    for(i=0;i<depth;i++) s+=" ";
    trace_list.push(s+txt);
  } else if (trace_flag && trace_method=="html") {
    for(i=0;i<depth;i++) s+="&nbsp;";
    trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");
  }
}

/* The variable number of a literal: 3 for both 3 and -3 */

function absvar(lit) {
  if (lit<0) return 0-lit;
  else return lit;
}

/* Print a literal using the original variable names, if we have them */

function showvar(x) {
  var nr,sign;
  if (x && origvars && origvars.length>0) {
    if (x<0) { nr=0-x; sign="-"; }
    else { nr=x; sign=""; }
    if (origvars.length>nr && origvars[nr])  return sign+origvars[nr];
    else return String(x);
  } else {
    return String(x);
  }
}

/* Print a clause in the internal format: the first two els are meta-info */

function clause_to_str(cl) {
  var i,s="";
  if (cl===true) return "tautology";
  if (!cl) return "empty";
  for(i=2;i<cl.length;i++) {
    s+=showvar(cl[i])+" ";
  }
  return s;
}

/* Print a plain list of literals, like the literals of a learned clause */

function lit_list_to_str(lst) {
  var i,s="";
  for(i=0;i<lst.length;i++) {
    s+=showvar(lst[i])+" ";
  }
  return s;
}


// ====== module end ==========

})(this.proplog_cdcl = {});


