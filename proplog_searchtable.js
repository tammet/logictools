/* 
  Pure truth table search solver for propositional logic,
  easy to hack and experiment with. 
  In most cases this method is inferior to DPLL.
  
  Use like this: proplog_searchtable.searchtable([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.searchtable=...  
  Fully self-contained, no dependencies.   
  Exports function searchtable.  
    
  See http://logictools.org and http://github.com/tammet/logictools 
  for UI and other tools.
  
  For the truth table search method, see
  http://logic.stanford.edu/intrologic/chapters/chapter_05.html
  
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
  
var truth_value_leaves_count=0; 
var truth_value_calc_count=0; 
  
// algorithm selection: "nodes" is almost always a much better choice
  
var truth_check_place="nodes"; // where is the value checked: either "nodes" or "leaves"
  
// ====== truth table search solver  ==========

/* 
  Check whether a clause set is satisfiable, by search through the truth
  value table: checking out all possible valuations of variables.
 
  Take 
    clauses: a clause set (array of integer arrays) like [[1,-2],[-2,1]] 
    maxvarnr: (optional) the maximal variable in clauses (integer) like 2.
    algorithm: (optional) by default ("nodes") the truth value is checked in each 
      search tree node; set to "leaves" to check in leaves only.
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

exports.searchtable = function (clauses,maxvarnr,algorithm,trace,varnames) {
  var i,j,c,nr,varvals,res,txt;
  // store algorithm choice, trace and origvars to globals
  truth_check_place=algorithm;
  if (trace) { trace_flag=true; trace_method=trace; }
  else { trace_flag=false; }
  if (varnames) origvars=varnames;
  else origvars=false;  
  // zero statistics counters
  truth_value_calc_count=0; 
  truth_value_leaves_count=0; 
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
  // start search  
  res= satisfiable_by_table_at(clauses,varvals,1,1,1) || 
       satisfiable_by_table_at(clauses,varvals,1,-1,1);
  
  txt="finished: evaluations count is "+truth_value_calc_count;
  txt+=", leaves count is "+truth_value_leaves_count;
  trace_list.push(txt);
  
  if (res) return [result_model,trace_list.join("\r\n")];
  else return [false,trace_list.join("\r\n")];
}

/* 
  Check clause set value at a given (partial) assignment of variables, with
  full search by recursively extending the assignment.
  Take:
    clauses: a clause set like [[1,-2],[-2,1]] 
    varvals: the (partial) assignment array of vars like [0,1,1,0,-1,...]
      where 1 means true, -1 means false, 0 means not assigned
    var: variable number (like 2) to assign next
    val: var value to assign next, either 1 (true) or -1 (false)

  Return 
    true iff the clause set is satisfiable for the given assignment (ie
      there is an evaluation of vars where the clause set is true)
    false when the clause set is contradictory or contingent
*/

function satisfiable_by_table_at(clauses,varvals,varnr,val,depth) {
  var tmp,errtxt;
  varvals[varnr]=val;
  if (varnr===varvals.length-1) truth_value_leaves_count++;
  // naive: evaluate only leaves; better: evaluate partial solutions
  if (trace_flag) print_trace(depth,"setting var "+showvar(varnr)+" to "+val);
  if (truth_check_place!=="leaves" || varnr===varvals.length-1) {    
    tmp=clauses_truth_value_at(clauses,varvals,depth); // check the value at a partial assignment    
    if (tmp===1) { store_model(varvals); varvals[varnr]=0; return true;}
    if (tmp===-1){ varvals[varnr]=0; return false;}
  }
  if (varnr<varvals.length-1) {
    if (satisfiable_by_table_at(clauses,varvals,varnr+1,1,depth+1) ||
        satisfiable_by_table_at(clauses,varvals,varnr+1,-1,depth+1)) {       
      //store_model(varvals);
      varvals[varnr]=0;          
      return true;
    }   
    varvals[varnr]=0;
    return false;        
  } else {
    // error case: should not happen
    errtxt="Error in the satisfiable_by_table algorithm";
    console.log(errtxt);
    show_process(errtxt);
  }
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

/* 
  Check clause set value at a given (partial) assignment of variables, 
  without search.

  Take:
    clauses: a clause set like [[1,-2],[-2,1]] 
    varvals: the (partial) assignment array of vars like [0,1,1,0,-1,...]
      where 1 means true, -1 means false, 0 means not assigned    
    depth: evaluation tree depth, used only for logging on console
  Return:
    1 if the clause set is satisfiable for the given assignment, ie
      there is an evaluation of vars where the clause set is true 
      (possible even for partial assigments)
    -1 if the clause set is not satisfiable for the given assignment, ie
      the assignment makes the clause set false (only possible for full assigments)
    0 if the (partial) assignment does not determine the value of the clause set 
*/

function clauses_truth_value_at(clauses,varvals,depth) {
  var i,j,nr,vval,polarity;
  var clause,clauseval,allvarsfound,allclausesfound;
  truth_value_calc_count++;
  allclausesfound=true;
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];        
    clauseval=0;
    allvarsfound=true;
    for (j=0; j<clause.length; j++) {
      nr=clause[j];
      polarity=1;
      if (nr<0) {nr=nr * -1; polarity=-1};
      vval=varvals[nr];
      if (vval===polarity) {
        clauseval=1;
        break;
      } else if (vval===0) {
        allvarsfound=false;
      }
    }
    if (clauseval!==1 && allvarsfound) {
      if (trace_flag) print_trace(depth,"value is false");
      return -1;
    }  
    if (!allvarsfound) allclausesfound=false;
  }
  if (allclausesfound) {
    if (trace_flag) print_trace(depth,"value is true");
    return 1;
  }  
  if (trace_flag) print_trace(depth,"value is undetermined");
  return 0;
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

})(this.proplog_searchtable = {});



