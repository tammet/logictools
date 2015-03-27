/* 
  DPLL solver for propositional logic, 
  easy to hack and experiment with.  
  
  Use like this: proplog_dpll.dpll([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.dpll=...  
  Fully self-contained, no dependencies.   
  Exports function dpll.  
    
  See http://logictools.org and http://github.com/tammet/logictools 
  for UI and other tools.
  
  For DPLL (Davis-Putnam-Logemann-Loveland) see 
  http://en.wikipedia.org/wiki/DPLL_algorithm
  
  Recommended to use with the accompanying proplog.html file providing 
  a basic user interface and other tools for propositional logic.           
  
  This software is covered by the MIT licence, see http://opensource.org/licenses/MIT
  or http://en.wikipedia.org/wiki/MIT_License
  
  Copyright (c) 2015 Tanel Tammet (tanel.tammet at gmail.com)
*/



(function(exports) {
  "use strict";
  
// ====== module start =========

// trace text and the resulting model:  
  
var trace_flag=false; // false if no trace
var trace_method="text"; // ok values: text, html or console
var trace_list=[];  // list of strings 
var origvars=[]; // original variable names to use in trace, if available and not false
var result_model=[]; // set by solver to a resulting model: values of vars
  
// statistical counts:

var unit_propagations_count=0;
var var_selections_count=0; 
var units_derived_count=0;   
var pure_derived_count=0;
var clauses_removed_count=0;
var max_depth_count=0;
  
var varactivities; // array of variable activities for preference, assigned later

// ====== improved dpll solver ==========

/* 
  Check whether a clause set is satisfiable, using an implementation 
  of the dpll (Davis-Putnam-Logemann-Loveland) procedure combining truth
  table search with the resolution-like unit propagation.

  This algorithm uses:
  - simple preprocessing before search starts: limited unit propagation/subsumption,
    tautology deletion and pure literal deletion
  - unit propagation during search
  - weighted selection of the next variable to split
  - learning variable weights: the last contradiction clause adds weights
    to the variables it contains
  - clauses are organized into lists of buckets for all vars, 
    containing all clauses where this var occurs: separately for pos and neg
    occurrences.
  - two watched literals per clause

  Clause learning and non-chronological backtracking are not implemented
  (see https://en.wikipedia.org/wiki/Conflict-Driven_Clause_Learning )

  See http://minisat.se/downloads/MiniSat.pdf for a good introduction
  to optimizing propositional solvers.

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

exports.dpll = function (clauses,maxvarnr,trace,varnames) {
  var varvals,occvars,posbuckets,negbuckets,derived,tmp;
  var i,res,txt;
  // store trace and origvars to globals
  if (trace) { trace_flag=true; trace_method=trace; }
  else { trace_flag=false; }
  if (varnames) origvars=varnames;
  else origvars=false;
  // zero statistics and trace globals
  unit_propagations_count=0; 
  var_selections_count=0;
  units_derived_count=0; 
  pure_derived_count=0;
  clauses_removed_count=0;
  max_depth_count=0;
  trace_list=[];
  result_model=[];
  // First add two meta-info els to the beginning of each clause:
  // the two meta-elements are later used for clause signature during optional
  // simplification and as watched literal pointers in the proper dpll search.
  // Also, get the nr of the largest variable in the clause set
  tmp=maxvar_and_meta(clauses);
  maxvarnr=tmp[0];
  clauses=tmp[1];  
  // create the arrays used during search
  derived=new Int32Array(maxvarnr+1); // used for units derived during propagation
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;
  // array used while preprocessing to count occurrences
  occvars=new Int32Array(maxvarnr+1);
  // buckets where a var occurs positively
  posbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) posbuckets[i]=[];
  // buckets where a var occurs negatively
  negbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) negbuckets[i]=[];
  // var activities indicate which var to pick next: larger is better
  varactivities=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varactivities[i]=1;
    
  // optional simplification: may be omitted
  
  clauses=simplify_clause_list(clauses,varvals,occvars,posbuckets,negbuckets,derived);
  if (clauses===false) {  // contradiction found
    if (trace_flag) trace_list.push("contradiction found during simplification");
    return [false,trace_list.join("\r\n")];
  } else if (clauses.length===0) { // no clauses remaining: a model found
    store_model(varvals);
    if (trace_flag) trace_list.push("assignment found during simplification");    
    return [result_model,trace_list.join("\r\n")];
  }
  
  // remove pure variables and build initial activities for vars
  clauses=count_occurrences(clauses,varvals,occvars,posbuckets,negbuckets,derived);
  if (clauses.length===0) { // no clauses remaining: a model found
    store_model(varvals);
    if (trace_flag) trace_list.push("assignment found during pure literal elimination");
    return [result_model,trace_list.join("\r\n")];
  }
  // assign clauses to buckets according to literal occurrences
  makebuckets(clauses,varvals,occvars,posbuckets,negbuckets,derived);   
  
  /*
  txt="preprocessing finished: " 
  txt+=", pure derived count is "+pure_derived_count;  
  txt+=", clauses removed count is "+clauses_removed_count+".";
  trace_list.push(txt);  
  */
  
  // full search
  res=satisfiable_at(0,0,clauses,varvals,occvars,posbuckets,negbuckets,derived);
  
  txt="search finished: unit propagations count is "+unit_propagations_count;
  txt+=", units derived count is "+units_derived_count;  
  txt+=", max depth is "+max_depth_count;  
  trace_list.push(txt);
  
  if (res) return [result_model,trace_list.join("\r\n")];
  else return [false,trace_list.join("\r\n")];
}


function satisfiable_at(derivedlen,depth,clauses,varvals,occvars,posbuckets,negbuckets,derived) {
  var queue,propres,nextvar,sign,errtxt,lit,i,satval,s;
  if (depth>max_depth_count) max_depth_count=depth; // statistics
  // functions without passing a variable to assign (then varnr==0)
  // call unit propagation    
  if (derivedlen!==0) {
    // assigned variable(s) passed
    if (trace_flag) {
      s="assigning var ";
      for(i=0;i<derivedlen;i++) s+=showvar(derived[i])+" ";
      print_trace(depth,s);
    }  
    propres=unit_propagate(derivedlen,depth,clauses,varvals,posbuckets,negbuckets,derived);
  } else {
    // no assigned variables
    if (trace_flag) print_trace(depth,"search called without assigning vars");
    propres=0; // 0 marks no unit propagation done
  }
  // unit propagation done with result propres  
  if (propres===true) { store_model(varvals); return true;}
  // if result false (-1) unit_propagate restores the varvals state itself
  if (propres===false)  return false;
  // find next unassigned var to split
  nextvar=next_var(clauses,varvals,occvars);
  if (nextvar===0) {
    // no more variables to split, no contradiction found   
    store_model(varvals);
    return true;
  }
  // start splitting
  if (trace_flag) print_trace(depth,"splitting variable "+showvar(nextvar));
  derived[0]=nextvar;
  satval=satisfiable_at(1,depth+1,clauses,varvals,occvars,posbuckets,negbuckets,derived);
  if (satval) return true;
  derived[0]=0-nextvar;
  satval=satisfiable_at(1,depth+1,clauses,varvals,occvars,posbuckets,negbuckets,derived);
  if (satval) return true;
  // not satisfiable at this valuation: restore vars
  if (typeof(propres)==="number") {
    // single unit 
    if (propres<0) varvals[0-propres]=0;
    else if (propres!==0) varvals[propres]=0; // if 0, no initial assignment passed
  } else {
    // list of units
    for(i=0;i<propres.length;i++) {
      lit=propres[i];
      if (lit<0) varvals[0-lit]=0;
      else varvals[lit]=0;
    } 
  } 
  return false;
}

/* Check whether clauses are satisfiable under the varvals assignment, without search.
   
  Iterate through all clauses and check whether 
   - all literals in the clause are assigned false: 
       undo derived units (set values in varvals to 0) and return false immediately
   - a clause contains literal assigned to true: 
       skip further actions on this clause
   - a single literal in the clause is unassigned, all the rest are assigned false: 
       derive this literal as a unit clause.

  In case at least one literal is derived during the process above, iterate the whole process
  until no more new literals are derived.

  Returns:
    1: all clauses were assigned true, hence the clause set is satisfiable.  
          The whole search will terminate after that.
    -1: clause set is contradictory. Derived units have been restored.
    a single derived var or a a list of derived variables:  
      the status of the clause set is undetermined. 
      The values of variables on the list will be restored (set to 0) during backtracking.

*/


function unit_propagate(derivedlen,depth,clauses,varvals,posbuckets,negbuckets,derived) {
  var i,j,dlit,negdlit,lit,nr,vval,polarity,derivednext,allclausesfound;
  var bucket,bucketlen,tmpbucket,clause,useclause,unassigned_count,unassigned_lit;
  var assigned,derived_units_txt,activity;
  unit_propagations_count++;   
  derived_units_txt=""; // used only for the trace: all the derived literals (signed vars)  
  derivednext=0; // next index of derived to use in the iteration
  // assign immediately all vars in the derived
  for(i=0; i<derivedlen ; i++) {
    lit=derived[i]; 
    if (lit<0) varvals[0-lit]=-1
    else varvals[lit]=1;
  }
  // the main loop is run, deriving new unit clauses, until either:
  // - the clause set is detected to be unsatisfiable
  // - there are no more derived unit clauses 
  while(derivednext<derivedlen) {        
    dlit=derived[derivednext++]; // take next el from derived
    negdlit=0-dlit;
    if (dlit<0) bucket=posbuckets[negdlit];
    else bucket=negbuckets[dlit]; 
    bucketlen=bucket[0]; // nr of used bucket elements: actual array is normally longer
    for (i=1; i<=bucketlen; i++) { // iterate over clauses in the bucket  
      clause=bucket[i];    
      useclause=true;
      unassigned_count=0; // count unassigned vars in clause
      unassigned_lit=0; // 0 means no unassigned vars found for this clause
      for (j=2; j<clause.length; j++) {
        // loop over a single clause in the bucket
        lit=clause[j];
        if (lit<0) {vval=varvals[0-lit]; polarity=-1}
        else {vval=varvals[lit]; polarity=1};
        if (vval===0) { 
          if (unassigned_count>0) {            
            //here we must change the watched literal
            if (clause[0]===negdlit) {
              //current watched is at meta position 0
              if (lit===clause[1]) lit=unassigned_lit; // cur lit is the other watched?
              clause[0]=lit; // change the watched literal
            } else {
              //current watched is at meta position 1
              if (lit===clause[0]) lit=unassigned_lit; // cur lit is the other watched?
              clause[1]=lit; // change the watched literal
            }             
            // add clause to new bucket              
            if (lit<0) tmpbucket=negbuckets[0-lit]; 
            else tmpbucket=posbuckets[lit];
            tmpbucket[0]++;
            tmpbucket[tmpbucket[0]]=clause;              
            // remove clause from current bucket: push the last el of bucket to this pos
            bucket[i]=bucket[bucketlen]; // move the last used bucket el to current el
            bucket[0]--;
            bucketlen--;
            i--; // the clause moved here from the end must be iterated over   
            // cannot derive anything from the clause
            useclause=false; 
            break; 
          } 
          unassigned_count++;          
          unassigned_lit=lit;
        } else if (vval===polarity) { 
          useclause=false; 
          break; 
        }
      }
      if (useclause) {
        // clause is not subsumed by varvals and has zero or one unassigned lit
        if (unassigned_count===0) {
          // clause is false: all literals were cut
          if (trace_flag) print_trace(depth,"value is false");          
          // restore varvals, bump activities and return false
          for(j=0;j<derivedlen;j++) {            
            lit=derived[j];
            if (lit<0) varvals[0-lit]=0;
            else varvals[lit]=0;
          }  
          // increase variable activities for this clause          
          activity=2*(Math.pow(unit_propagations_count,1.5));
          for(j=2; j<clause.length; j++) {
            lit=clause[j];            
            if (lit<0) varactivities[0-lit]+=activity;
            else varactivities[lit]+=activity;
          }          
          return false;
        } 
        // here unassigned_count==1, i.e. unassigned_lit is a derived literal
        units_derived_count++;
        derived[derivedlen]=unassigned_lit; 
        derivedlen++;
        if (unassigned_lit<0) {nr=0-unassigned_lit; polarity=-1}
        else {nr=unassigned_lit; polarity=1};
        varvals[nr]=polarity;
        if (trace_flag) derived_units_txt+=unassigned_lit+" ";
      }     
    }
    // bucket loop ended    
  }
  // main loop ended, not detected to be unsatisfiable
  if (trace_flag) {
    print_trace(depth,"value is undetermined");
    if (derived_units_txt.length>0) print_trace(depth,"derived units "+derived_units_txt);
  }
  // if just one assigned, return this literal
  if (derivedlen===1) return derived[0];
  // else copy all assigned and return the list of all assigned
  assigned=new Int32Array(derivedlen);
  for(i=0;i<derivedlen;i++) assigned[i]=derived[i];
  return assigned;
}      

/* Find the next variable to be assigned or split.
  
  Returns:    
    a number: the (positive) variable number to be split.
*/

function next_var(clauses,varvals,occvars) {
  var i,activity,bestfound,maxactivity;
  var l_varactivities=varactivities;
  
  var_selections_count++;
  maxactivity=-1000;
  bestfound=0;
  for(i=1;i<varvals.length;i++) {
    if (varvals[i]!==0) continue;
    activity=l_varactivities[i];
    if (activity>=maxactivity) {
      maxactivity=activity;
      bestfound=i;
    }   
  }
  return bestfound; 
}


/* 
  Store the current valuation of variables to be printed out later as a model.
*/

function store_model(varvals) {
  var i;
  //result_model=[];
  for(i=1;i<varvals.length;i++) {
    // store assigned values as -1, 3, -4, ...
    if (varvals[i]!==0) result_model.push(showvar(i*varvals[i]));
  }  
}

// ================= preprocessing phase ========================

/* Adds two extra meta-info elements to the beginning of each clause,
   returning a new clause set with the augmented clauses.

   The two meta-elements are later used for clause signature during optional
   simplification and as watched literal pointers in the proper dpll search.   
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
*/ 

function simplify_clause_list(clauses,varvals,occvars,posbuckets,negbuckets,derived) { 
  var clauses2,i,j,k,clause,lit,nlit,nr,sign,remove,cuts,dups,nlen,nc,unsat,s;  
  clauses=clauses.sort(function(a,b){return a.length-b.length});  
  // loop over clauses to remove tautologies and duplicate literals
  // and to perform unit subsumption and cutoff
  unsat=false;
  clauses2=[];
  for(i=0;i<clauses.length;i++) {
    //console.log("clause i "+i+" "+clause_to_str(clauses[i]));
    clause=clauses[i];
    remove=false;
    cuts=0;
    dups=0;
    for(j=2;j<clause.length;j++) {
      lit=clause[j];
      nlit=0-lit;
      if (lit<0) {nr=0-lit; sign=-1; }
      else {nr=lit; sign=1; }
      if (varvals[nr]===sign) { remove=true; break; } // subsumed
      if (varvals[nr]===0-sign) { clause[j]=0; cuts++; continue; } // cut off            
      for(k=2;k<j;k++) { // check for tautology and duplicate literals
        if(clause[k]===nlit) { remove=true; break; }
        if(clause[k]===lit) { clause[j]=0; dups++; }
      }  
      if (remove) break; // do not keep tautologies
    }
    //console.log("cuts "+cuts+" dups "+dups+" remove "+remove);
    if (remove) {
      clauses_removed_count++;
      continue;    
    }  
    nlen=clause.length-(cuts+dups);
    if (nlen===2) {
      unsat=true;
      return false;
    }  
    if (nlen===3) {
      // unit
      units_derived_count++;
      for(k=2;k<clause.length;k++) {
        if (clause[k]!==0) {lit=clause[k]; break; }
      }
      //console.log("derived unit "+lit);
      if (lit<0) {nr=0-lit; sign=-1; }
      else {nr=lit; sign=1; }
      varvals[nr]=sign;
      continue;
    }
    if (nlen!==clause.length) {
      // some literals were removed
      nc=new Int32Array(nlen);
      nc[0]=clause[0];
      nc[1]=clause[1];
      k=0;
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
      if (varvals[i]!==0) s+=" "+i; //showvar(i*varvals[i])+" ";
    }  
    print_trace(0,s);
    console.log(s);
  } 
  return clauses2;
}

/* count literal occurrences to build two things:
   - a global list purevars of pure vars (vars occurring only positively or negatively)
   - the initial global varactivities list for vars used for selecting the next var

   It returns the clause list where all the clauses containing a pure var have been
   removed. If no pure vars found, it will be the input list.
*/
 
function count_occurrences(clauses,varvals,occvars,posbuckets,negbuckets,derived) {
  var clauses2,i,j,k,clause,lit,nr,sign,remove;
  var clen,vval,oval,bonus,purevars,s,maxact,tmp;
  
  // detect free vars (i.e. occurring only negatively or only positively)
  // and calculate initial activities for vars
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];
    clen=clause.length;  
    for (j=2; j<clen; j++) {
      lit=clause[j];
      if (lit<0) {nr=0-lit; sign=-1}
      else {nr=lit; sign=1};
      vval=varvals[nr];
      if(vval===0) {
        oval=occvars[nr];
        if (oval===0) occvars[nr]=sign;
        else if (oval===0-sign) occvars[nr]=2; // 2 marks both polarities occur
        else if (oval>=2) {
          if (clen<5) bonus=20;
          else if (clen<6) bonus=15;
          else {
            bonus=10-(clen-2);
            if (bonus<0) bonus=1;
          }
          occvars[nr]=occvars[nr]+bonus;
        }  
      }  
    }   
  }
  // store occvars info to varactivities,
  // store pure vars to purevars and assign to varvals
  purevars=[];
  maxact=1;
  for(i=1;i<occvars.length;i++) {
    oval=occvars[i];
    if (oval<2) {
      purevars.push(i);
      if (oval<0) varvals[i]=-1;
      else varvals[i]=1;
      varactivities[i]=0;
    } else  {
      if (varvals[i]!==0) {
        varactivities[i]=0;
      } else {
        varactivities[i]=occvars[i];
        if (varactivities[i]>maxact) maxact=varactivities[i];
      }  
    }  
  }
  // optionally normalize varactivities
  /*
  for(i=1;i<varactivities.length;i++) {
    tmp=(varactivities[i]/maxact)*10;
    varactivities[i]=tmp;
  }
  */
  // remove clauses containing pure vars
  if (purevars.length>0) {
    pure_derived_count+=purevars.length;
    if (trace_flag) {
      s="pure vars eliminated: ";
      for(i=0;i<purevars.length;i++) s+=showvar(purevars[i])+" ";
      print_trace(0,s);
    }  
    clauses2=[];
    for (i=0; i<clauses.length; i++) {      
      clause=clauses[i];
      remove=false;
      for (j=2; j<clause.length; j++) {
        lit=clause[j];
        if (lit<0) nr=0-lit;
        else nr=lit;
        if (varactivities[nr]===0) { 
          clauses_removed_count++;
          remove=true;  
          break; 
        }
      }
      if (!remove) clauses2.push(clause);
    }
    clauses=clauses2;    
  }
  if (trace_flag) {
    s="initial variable activities: ";
    for(i=1;i<varactivities.length;i++) {
      s+=showvar(i)+":"+varactivities[i]+" ";
    }
    print_trace(0,s);
  }
  return clauses;
}  

/* creates the global posbuckets and negbuckets arrays for all vars: 
   each bucket is an array of clauses contaning the literal, either
   positively (posbuckets) or negatively (negbuckets).

   The first el is the number of actually used clauses in the bucket.
   Then come used clauses, finally placeholders to be potentially
   filled later.
*/


function makebuckets(clauses,varvals,occvars,posbuckets,negbuckets,derived) {
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


 
// ======== optional trace printing ============


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

function clause_to_str(cl) {
  var i,s="";
  if (cl===true) return "tautology";
  if (!cl) return "empty";
  for(i=2;i<cl.length;i++) {    
    s+=showvar(cl[i])+" ";
  }  
  return s;
}

function array_to_str(cl) {
  var i,s="";
  if (cl===true) return "true";
  if (!cl) return "[]";
  for(i=0;i<cl.length;i++) {    
    s+=cl[i]+" ";
  }  
  return s;
}

function array_list_to_str(arr) {
  var i,s="";
  for(i=0;i<arr.length;i++) {    
    s+=array_to_str(arr[i])+"; \n";
  }  
  return s;
}

function clause_list_to_str(lst) {
  var i,s="[";
  for(i=0;i<lst.length;i++) {
    s+="["+clause_to_str(lst[i])+"]";
  }
  return s+"]";
}  

function clause_list_list_to_str(lst) {
  var i,s="[";
  for(i=0;i<lst.length;i++) {
    s+=clause_list_to_str(lst[i]);
  }
  return s+"]";
}


// ====== module end ==========

})(this.proplog_dpll = {});



