/* 
  Naive DPLL solver for propositional logic,
  easy to hack and experiment with. 
  
  Use like this: proplog_naivedpll.naivedpll([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.naivedpll=...
  Fully self-contained, no dependencies.   
  Exports naivedpll.   
    
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
var units_derived_count=0;   
var max_depth_count=0; 

// ========== naive dpll solver ==========

/* 
  Check whether a clause set is satisfiable or contradictory, 
  using a naive implementation 
  of the dpll (Davis-Putnam-Logemann-Loveland) procedure combining truth
  table search with the resolution-like unit propagation.

  The standard pure-literal rule is not implemented in this naive version, 
  since it is not really crucial for the algorithm.
  
  The code is very similar to the pure table solver, except we use
  a unit-propagating, derived-varlist-returing satisfiable_at.
  
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

exports.naivedpll = function (clauses,maxvarnr,trace,varnames) {
  var i,j,c,nr,res,varvals,txt;
  // store trace and origvars to globals
  if (trace) { trace_flag=true; trace_method=trace; }
  else { trace_flag=false; }
  if (varnames) origvars=varnames;
  else origvars=false;
  // zero statistics globals
  unit_propagations_count=0; 
  units_derived_count=0;
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
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;
  // no variable assigned here: dpll_satisfiable_at 
  // unit-propagates and then selects an unassigned variable to split
  res=satisfiable_at(clauses,varvals,0,0,0);
  
  txt="finished: unit propagations count is "+unit_propagations_count;
  txt+=", units derived count is "+units_derived_count;
  txt+=", max depth is "+max_depth_count;  
  trace_list.push(txt);
  
  if (res) return [result_model,trace_list.join("\r\n")];
  else return [false,trace_list.join("\r\n")];
}


function satisfiable_at(clauses,varvals,varnr,val,depth) {
  var propres,i,nextvar,sign,errtxt;
  if (depth>max_depth_count) max_depth_count=depth; // statistics
  // functions ok without passing a variable to assign (if varnr==0)
  if (varnr!==0) {
    // assigned variable passed
    if (trace_flag) print_trace(depth,"setting var "+showvar(varnr)+" to "+val);
    varvals[varnr]=val; 
  } else {
    if (trace_flag) print_trace(depth,"search called without setting a var before");
  }
  // call unit propagation
  propres=unit_propagate(clauses,varvals,depth);
  if (propres===1) { store_model(varvals); varvals[varnr]=0; return true;}
  // if result false (-1) unit_propagate restores the varvals state itself
  if (propres===-1){ varvals[varnr]=0; return false;} 
  // find next unassigned var to split
  nextvar=0;
  for(i=1;i<varvals.length;i++) {
    if (varvals[i]===0) { nextvar=i; break; }
  }  
  if (nextvar!==0) {
    if (trace_flag) print_trace(depth,"splitting variable "+showvar(nextvar));
    if (satisfiable_at(clauses,varvals,nextvar,1,depth+1) ||
        satisfiable_at(clauses,varvals,nextvar,-1,depth+1)) {
      // not necessary to restore split var: search is halted anyway                    
      return true;
    }   
    varvals[nextvar]=0; // restore split var
    for(i=0;i<propres.length;i++) varvals[propres[i]]=0; // restore derived vars
    return false;        
  } else {
    // error case: should not happen
    errtxt="Error in the satisfiable_at";
    console.log(errtxt);
    show_process(errtxt);
  }
}

/* Check whether clauses are satisfiable under the varvals assignment, without search.
   
  Iterate through all clauses and check whether 
   - all literals in the clause are assigned false: 
       undo derived units (set values in varvals to 0) and return false immediately
   - a clause contains a literal assigned true: 
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

function unit_propagate(clauses,varvals,depth) {
  var i,j,lit,nr,vval,polarity;
  var clause,clauseval,unassigned_count,unassigned_lit,allvarsfound,allclausesfound;
  var derived_vars,derived_queue,derived_units_txt;
  unit_propagations_count++;  
  derived_vars=[]; // all vars with a value derived in the forthcoming main loop
  derived_units_txt=""; // used only for the trace: all the derived literals (signed vars)  
  // the main loop is run, deriving new unit clauses, until either:
  // - the clause set is detected to be unsatisfiable
  // - the clause set is detected to be satisfiable
  // - there are no more derived unit clauses
  while(true) {
    allclausesfound=true; // set to false if we find an undetermined clause
    derived_queue=[]; // derived units (literals) during one iteration 
    for (i=0; i<clauses.length; i++) {
      // loop over all clauses
      clause=clauses[i];        
      clauseval=0;
      unassigned_count=0; // count unassigned vars in clause
      unassigned_lit=0; // 0 means none found for this clause
      for (j=0; j<clause.length; j++) {
        lit=clause[j];
        if (lit<0) {nr=0-lit; polarity=-1}
        else {nr=lit; polarity=1};
        vval=varvals[nr];
        if (vval===polarity) {
          clauseval=1;
          break;
        } else if (vval===0) {       
          unassigned_count++;
          unassigned_lit=lit;        
        }
      }
      if (clauseval===1) continue; // clause is subsumed
      // clause is not subsumed by varvals
      if (unassigned_count===0) {
        if (trace_flag) print_trace(depth,"value is false");
        for(j=0;j<derived_vars.length;j++) varvals[derived_vars[j]]=0; // restore derived
        return -1;
      } else if (unassigned_count===1) {
        // unassigned_lit is a derived literal
        units_derived_count++;
        derived_queue.push(unassigned_lit);
      }        
      if(unassigned_count!==0) allclausesfound=false; // some literals were not assigned
    }
    // all clauses have been looped over
    if (allclausesfound) {
      // all clauses were subsumed or all the variables in a clause had a value
      if (trace_flag) print_trace(depth,"value is true");
      // no need to restore varvals: whole search finished
      return 1;
    }
    // in case there are any derived units present, store to varvals and iterate the main loop
    if (derived_queue.length===0) {
      // nothing derived, terminate loop
      break;
    } else {
      // some units were derived: iterate the main loop
      for(j=0;j<derived_queue.length;j++) {
        lit=derived_queue[j];
        if (lit<0) {nr=0-lit; polarity=-1}
        else {nr=lit; polarity=1};
        varvals[nr]=polarity;
        derived_vars.push(nr);
        if (trace_flag) derived_units_txt+=showvar(lit)+" ";
      }      
    }
  }
  // main loop ended
  if (trace_flag) {
    print_trace(depth,"value is undetermined");
    if (derived_vars.length>0) print_trace(depth,"derived units "+derived_units_txt);
  }    
  return derived_vars;
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


// ====== module end ==========

})(this.proplog_naivedpll = {});



