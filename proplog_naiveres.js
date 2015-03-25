/* 
  Naive resolution method solver for propositional logic,
  easy to hack and experiment with. 
  For notrivial formulas this solver is really slow.
  
  Use like this: proplog_naiveres.naiveres([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.naiveres=...
  Fully self-contained, no dependencies.   
  Exports function resolution.       
    
  See http://logictools.org and http://github.com/tammet/logictools 
  for UI and other tools.
  
  For the resolution method, see 
  http://en.wikipedia.org/wiki/Resolution_%28logic%29
  
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
  
var selected_clauses_count=0; 
var generated_clauses_count=0;
var kept_clauses_count=0; 

// ====== naive resolution solver ==========

/* Full resolution search for contradiction. 
  
  Uses a given-clause algorithm and does not use any optimisations, 
  except the forward subsumption check of a selected usable clause 
  with all processed clauses (this should guarantee termination of the search,
  given enough time and space).

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
    result is a _partial_ model (list of signed literals), maybe even just [] 
      if the clause set has a model
    
    tracetext is a human-readable string containing either only statistics 
      or trace+statistics: the tracetext format depends on the 
      passed trace parameter    

*/

exports.naiveres = function (clauses,maxvarnr,trace,varnames) {
  var usable_clauses, processed_clauses, selected, processed;
  var tmp_array;
  var p,found,i,j,sl,nsl,derived,result,txt;
  // store trace and origvars to globals
  if (trace) { trace_flag=true; trace_method=trace; }
  else { trace_flag=false; }
  if (varnames) origvars=varnames;
  else origvars=false; 
  // zero statistics
  selected_clauses_count=0; 
  generated_clauses_count=0;
  kept_clauses_count=0;
  trace_list=[];
  result_model=[];
  // prepare working arrays
  processed_clauses=[]; 
  usable_clauses=clauses;  
  tmp_array=new Int32Array(maxvarnr*2+1); // used during clause merge
  // main loop runs until no more usable clauses: if this happens, clause set is satisfiable
  result=true; // unless made to false later
  while(usable_clauses.length>0) {
    selected=usable_clauses.shift(); // remove and return first el
    if (trace_flag) print_trace(0,"selected "+clause_to_str(selected));
    // check whether the selected clause is subsumed by some processed clause
    found=false;
    for(p=0;p<processed_clauses.length;p++) {
      if (naive_subsumed(processed_clauses[p],selected)) {found=true; break;}
    }
    if (found) {
      // do not use this selected clause, just throw away
      if (trace_flag) print_trace(1," was subsumed");
      continue; 
    }  
    selected_clauses_count++;
    // resolve all processed clauses with the selected clause
    for(p=0;p<processed_clauses.length;p++) {
      processed=processed_clauses[p];     
      if (trace_flag) print_trace(2,"processed "+clause_to_str(processed));
      // do all resolution steps for selected and processed
      for(i=0;i<selected.length;i++) {
        sl=selected[i];
        nsl=0-sl;
        for(j=0;j<processed.length;j++) {          
          if (nsl===processed[j]) {
            generated_clauses_count++;
            derived=naive_merge_rest(selected,processed,i,j,tmp_array);
            if (trace_flag) print_trace(4,"derived "+clause_to_str(derived));
            if (derived===false) { result=false; break; } // contradiction found
            if (derived===true) continue; // tautology
            kept_clauses_count++;
            usable_clauses.push(derived);                                    
          }          
        }
      }
      if (!result) break;
    }
    // push the selected clause (removed from usable by now) to processed
    if (!result) break;
    processed_clauses.push(selected);
  }
  
  // main loop ended
  
  txt="finished: selected clauses: "+selected_clauses_count;
  txt+=", generated clauses: "+generated_clauses_count;
  txt+=", kept clauses: "+kept_clauses_count;
  trace_list.push(txt);
  
  if (result) { 
    // copy derived units to a result_model (here this is only a partial model)
    result_model=true;    
    return [result_model,trace_list.join("\r\n")];
  }  
  else {
    // contradiction found
    return [false,trace_list.join("\r\n")];  
  }
}


/* Merge resolvents, eliminating vars which are cut off and checking for
  tautology. Take
  c1: first clause
  c2: second clause
  i1: cutoff literal index in c1
  i2: cutoff literal index in c1
  tmp_array: int32 array for temporarily collecting c2 vars 
  
  Return: either 
    false : empty clause (contradiction) derived
    true: either tautology or subsumed by a unit clause
    an array of merged literals

  Examples where the first literals are cut:
  [1,2,3] and [-1,2,4] gives [2,3,4]
  [1,2,3] and [-1] gives [2,3]
  [1,2,3] and [-1,-1,4] gives [-1,2,3,4]
  [1,2,3] and [-1,1,4] gives [1,2,3,4]
*/

function naive_merge_rest(c1,c2,i1,i2,tmp_array) {
  var varcount,num,c,pos,i,j,l,nl,res,found;
  varcount=0; // nr of literals in which are merged to the result
  // handle clauses c1 (num=1) and c2 (num=2)
  for(num=1;num<3;num++) {
    if (num===1) { c=c1; pos=i1; }
    else { c=c2; pos=i2; }
    for (i=0;i<c.length;i++) {
      if(i===pos) continue; // do not copy the cut literal
      l=c[i]; // signed literal   
      nl=(0-l); // negated literal
      // check if var present in tmp_array of already merged literals
      found=false;
      for(j=0;j<varcount;j++) {      
        if (tmp_array[j]===l) {found=true; break;} // already have this var
        if (tmp_array[j]===nl) {return true; } // result clause is a tautology
      }
      if (!found) tmp_array[varcount++]=l;
    }      
  }   
  // tmp_array now contains all kept literals
  if (varcount===0) return false; // empty clause derived
  // make a fresh array res of a right size   
  res=new Int32Array(varcount); 
  for(j=0;j<varcount;j++) res[j]=tmp_array[j];  // copy collected vars
  return res;
}

/* Return true if clause c1 subsumes clause c2, false otherwise:   
   c1 subsumes c2 iff c1 is a subset of c2, like [2,-1] subsumes [-1,3,2,-5]
*/

function naive_subsumed(c1,c2) {  
  var i,j,lit,found;
  if (c1.length>c2.length) return false;  
  j=0;
  // do all the c1 literals occur in c2?
  for (i=0;i<c1.length;i++) {
    lit=c1[i];    
    found=false;
    for(j=0;j<c2.length; j++) {
      if (c2[j]===lit) {found=true; break; }      
    }
    if (!found) return false;
  }
  return true;
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

// ====== module end ==========

})(this.proplog_naiveres = {});



