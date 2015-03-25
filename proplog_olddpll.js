/* 
  Old-style DPLL solver for propositional logic, 
  easy to hack and experiment with.  
  
  Use like this: proplog_olddpll.olddpll([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.olddpll=...  
  Fully self-contained, no dependencies.   
  Exports function olddpll.  
    
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
var max_depth_count=0;

// ====== old-style dpll solver ==========

/* 
  Check whether a clause set is satisfiable, using an implementation 
  of the dpll (Davis-Putnam-Logemann-Loveland) procedure combining truth
  table search with the resolution-like unit propagation.

  This algorithm uses several old-style optimizations:
  - unit propagation
  - pure literal rule
  - weighted selection of the next variable to split
  - clauses are organized into lists of buckets for all vars, 
    containing all clauses where this var occurs: separately for pos and neg
    occurrences.
  - variables derived during unit propagation are used immediately
  
  This old-style solver does not use modern optimizations like two-literal 
  watching, clause learning, preferring recently cut literals,
  clause set preprocessing.

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

exports.olddpll = function (clauses,maxvarnr,trace,varnames) {
  var i,j,k,found,res,varvals,occvars,posbuckets,negbuckets,derived;
  var c,lit,nlit,nr,sign,nextvar,clauses2,tmp,txt;
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
  max_depth_count=0;
  trace_list=[];
  result_model=[];
  // find maxvarnr if not given
  if (!maxvarnr) {
    maxvarnr=0;
    for(i=0;i<clauses.length;i++) {
      c=clauses[i];
      for(j=0;j<c.length;j++) {
        if (c[j]<0) nr=0-c[j];
        else nr=c[j];
        if (nr>maxvarnr) maxvarnr=nr;        
      }
    }
  }
  // create the arrays used during search
  derived=new Int32Array(maxvarnr+1); // used for units derived during propagation
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;
  // temporary array used for finding the next variable to split
  occvars=new Int32Array(maxvarnr+1);
  // buckets where a var occurs positively
  posbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) posbuckets[i]=[];
  // buckets where a var occurs negatively
  negbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) negbuckets[i]=[];
  
  // preprocess clauses
  clauses=preprocess(clauses,varvals,occvars,posbuckets,negbuckets,derived);
  // full search
  res=satisfiable_at(clauses,varvals,0,0,0,occvars,posbuckets,negbuckets,derived);
  
  txt="finished: unit propagations count is "+unit_propagations_count;
  txt+=", units derived count is "+units_derived_count; 
  txt+=", var selections count is "+var_selections_count;
  txt+=", pure literal count is "+pure_derived_count;
  txt+=", max depth is "+max_depth_count;  
  trace_list.push(txt);
  
  if (res) return [result_model,trace_list.join("\r\n")];
  else return [false,trace_list.join("\r\n")];
}


function preprocess(clauses,varvals,occvars,posbuckets,negbuckets,derived) {
  var propres,nextvar,sign,errtxt,depth;
  var clauses2,i,j,k,c,lit,nlit,found;
  // loop over clauses and distribute them to buckets, removing tautologies
  clauses2=[];
  for(i=0;i<clauses.length;i++) {
    c=clauses[i];
    for(j=0;j<c.length;j++) {
      lit=c[j];
      nlit=0-lit;
      found=false;
      for(k=0;k<j;k++) { // check for tautology
        if(c[k]===nlit) { found=true; break; }
      }  
      if (found) continue; // do not keep tautologies
      if(lit<0) negbuckets[nlit].push(c);
      else posbuckets[lit].push(c);
      clauses2.push(c);
    }
  }
  
  return clauses2;
}


function satisfiable_at(clauses,varvals,varnr,val,depth,occvars,posbuckets,negbuckets,derived) {
  var queue,propres,nextvars,nextvar,sign,errtxt,lit,i,satval;
  if (depth>max_depth_count) max_depth_count=depth; // statistics
  // functions without passing a variable to assign (then varnr==0)
  // call unit propagation
  if (varnr!==0) {
    // assigned variable passed
    if (trace_flag) print_trace(depth,"assigning var "+showvar(varnr)+" to "+val);
    //queue=[varnr*val];        
    derived[0]=varnr*val;
    propres=unit_propagate(clauses,varvals,1,depth,posbuckets,negbuckets,derived);
  } else {
    // no assigned variables
    if (trace_flag) print_trace(depth,"search called without assigning a var before");
    propres=0; // 0 marks no unit propagation done
  }
  // unit propagation done with result propres  
  if (propres===true) { store_model(varvals); return true;}
  // if result false (-1) unit_propagate restores the varvals state itself
  if (propres===false)  return false;
  // find next unassigned var to split
  nextvars=next_vars(clauses,varvals,occvars);
  if (nextvars===0) {
    // no more variables to split, no contradiction found   
    store_model(varvals);
    return true;
  }
  if ((typeof nextvars) !== "number") {
    // pure literal found
    pure_derived_count++;
    nextvar=nextvars[0]; // literal was encoded into a single-element array
    if (nextvar<0) {nextvar=0-nextvar; sign=0-1; }
    else { sign=1; }
    if (trace_flag) print_trace(depth,"pure variable "+showvar(nextvar)+", sign "+sign);
    if (satisfiable_at(clauses,varvals,nextvar,sign,depth+1,occvars,posbuckets,negbuckets,derived)) {
      return true;
    } else {
      // restore vars and return false
      if (typeof(propres)==="number") {
        if (propres<0) varvals[0-propres]=0;
        else if (propres!==0) varvals[propres]=0; // if 0, no initial assignment passed
      } else {
        for(i=0;i<propres.length;i++) {
          lit=propres[i];
          if (lit<0) varvals[0-lit]=0;
          else varvals[lit]=0;
        } 
      } 
      return false;         
    }      
  } 
  // normal variable found
  nextvar=nextvars;
  if (trace_flag) print_trace(depth,"splitting variable "+showvar(nextvar));
  // start splitting
  if (trace_flag) print_trace(depth,"splitting variable "+showvar(nextvar));
  satval=satisfiable_at(clauses,varvals,nextvar,1,depth+1,occvars,posbuckets,negbuckets,derived);
  if (satval) return true;
  satval=satisfiable_at(clauses,varvals,nextvar,-1,depth+1,occvars,posbuckets,negbuckets,derived);
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
    a list of derived variables:  the status of the clause set is undetermined. 
      The values of variables on the list will be restored (set to 0) during backtracking.

*/

function unit_propagate(clauses,varvals,derivedlen,depth,posbuckets,negbuckets,derived) {
  var i,j,lit,nr,vval,polarity,derivednext,allclausesfound;
  var bucket,clause,useclause,unassigned_count,unassigned_lit;
  var assigned,derived_units_txt;
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
    lit=derived[derivednext++]; // take next el from derived
    //print_trace(5,"queue iteration with lit "+lit);
    if (lit<0) bucket=posbuckets[0-lit];
    else bucket=negbuckets[lit]; 
    //print_trace(5,"queue bucket "+clause_list_to_str(bucket));
    for (i=0; i<bucket.length; i++) { // iterate over clauses in the bucket  
      clause=bucket[i];        
      //print_trace(5,"bucket iteration with clause"+clause_to_str(clause));
      useclause=true;
      unassigned_count=0; // count unassigned vars in clause
      unassigned_lit=0; // 0 means no unassigned vars found for this clause
      for (j=0; j<clause.length; j++) {
        // loop over a single clause in the bucket
        lit=clause[j];
        if (lit<0) {vval=varvals[0-lit]; polarity=-1}
        else {vval=varvals[lit]; polarity=1};
        if (vval===0) { 
          if (unassigned_count>0) { useclause=false; break; } // no need to use
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
          // restore varvals and return false
          for(j=0;j<derivedlen;j++) {            
            lit=derived[j];
            if (lit<0) varvals[0-lit]=0;
            else varvals[lit]=0;
          }  
          return false;
        } 
        // here unassigned_count==1, i.e. unassigned_lit is a derived literal
        units_derived_count++;
        derived[derivedlen]=unassigned_lit; 
        derivedlen++;          
        //print_trace(5,"queue.push "+unassigned_lit);
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
  
  Return an unassigned pure (singed) literal, if such exists: pure literal is 
  a literal occurring only negatively or positively. No splitting needed for
  this literal: it will be assigned as is.

  Otherwise return a variable (positive) to be split, ie tested both positively
  and negatively. The variable is selected based on the occurrence statistics,
  preferring a variable occurring more and in shorter clauses.
  
  occvars is a temporary array used only in this function. 
  The values in occvars are: 0 no occurrences, -1/1 positive/negative occ only, 2 and more: both
    polarities occ with bonus count

  Returns:
    a one element-list like [-4]: contains the pure signed literal to be assigned next
    a number: the (positive) variable number to be split.
*/

function next_vars(clauses,varvals,occvars) {
  var i,j,lit,nr,vval,oval,polarity,bonus;
  var clause,clauseval,clen,blen,queue;
  
  //print_trace(6,"nextvar varvals "+clause_to_str(varvals));
  // for(i=1;i<varvals.length;i++) if(varvals[i]===0) return i;
  var_selections_count++;
  for(i=0;i<occvars.length;i++) occvars[i]=0;
  // find pure literals and calculate bonuses, storing to occvars;
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];        
    clauseval=0;      
    clen=clause.length;
    blen=clen;
    // determine if clause subsumed and the remaining length blen after cutting
    for (j=0; j<clen; j++) {
      lit=clause[j];
      if (lit<0) {nr=0-lit; polarity=-1}
      else {nr=lit; polarity=1};
      vval=varvals[nr];
      if (vval===polarity) {
        clauseval=1;
        break;
      } else if (vval===0-polarity) {
        blen--;
      }
    }  
    if (clauseval===0 && blen>0) {
      // not subsumed, pass again for unassigned vars
      for (j=0; j<clen; j++) {
        lit=clause[j];
        if (lit<0) {nr=0-lit; polarity=-1}
        else {nr=lit; polarity=1};
        vval=varvals[nr];
        if(vval===0) {
          oval=occvars[nr];
          if (oval===0) occvars[nr]=polarity;
          else if (oval===0-polarity) occvars[nr]=2; // 2 marks both polarities occur
          else if (oval>=2) {
            if (blen<3) bonus=20;
            else if (blen<4) bonus=15;
            else {
              bonus=10-blen;
              if (bonus<0) bonus=1;
            }
            occvars[nr]=occvars[nr]+bonus;
          }  
        }  
      }
    }
  } 
  // now check if we have a pure literal and also find a normal var with the max bonus
  bonus=0;
  nr=0;
  queue=[];
  for(i=1;i<occvars.length;i++) {
    oval=occvars[i];
    if (oval===0) continue;
    if (oval<2 && varvals[i]===0) queue.push(oval*i); // pure literal is returned as a signed single-el list
    if (oval>bonus && varvals[i]===0) {bonus=oval; nr=i;}    
  } 
  if (queue.length!==0) return queue;
  // single var with max bonus  
  if (nr<0) return 0-nr;
  else if (nr>0) return nr;
  else {
    for(i=1;i<varvals.length;i++) if(varvals[i]===0) return i;
  }
  return 0; // all vars are assigned
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
  for(i=0;i<cl.length;i++) {    
    s+=showvar(cl[i])+" ";
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

})(this.proplog_olddpll = {});



