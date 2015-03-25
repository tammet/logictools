/* 
  Resolution method solver for propositional logic,
  easy to hack and experiment with. 
  In most cases this method is inferior to DPLL.     
  
  Use like this: proplog_res.resolution([[-1,2],[1],[-2]])
  
  Optional arguments and other details below, before exports.resolution=...  
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
  
// ====== better resolution solver ==========

/* Full resolution search for contradiction.
  
  Uses a given-clause algorithm and several optimisations:
    - preprocessing clauses
    - literals in clauses are ordered like [-3-1,2,5] 
    - ordered resolution: use only the first literal of a clause
    - always selecting the shortest usable clause as given
    - storing and simplification by unit clauses (assigned variables)
    - forward subsumption of selected clauses and partial backward-subsumption

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
    result is true if the clause set has a model, but we do not know the model
    result is a _partial_ model (list of signed literals), maybe even just [] 
      if we know a (partial) model  for the clause set
    
    tracetext is a human-readable string containing either only statistics 
      or trace+statistics: the tracetext format depends on the 
      passed trace parameter
*/

exports.resolution = function (clauses,maxvarnr,trace,varnames) {
  var varvals,usable_clauses, processed_clauses, selected, processed; 
  var posbuckets,negbuckets,bucket,poscount,txt;
  var tmp_array, var_vals;
  var i,j,c,lit,s,vn,p,sl,nsl,nr,sign,derived,kept,l,horn_flag,result;
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
  tmp_array=new Int32Array(maxvarnr*2+1); // used during clause merge and preprocessing
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1); // unit clauses give values to vars
  for(i=0;i<maxvarnr+1;i++) varvals[i]=0;
  usable_clauses=new Array(100);
  for(i=0;i<100;i++) usable_clauses[i]=[];  // sublists of usable_clauses  
  
  // ------- preprocessing phase -------
  
  // first pass over clauses stores all unit clauses, checks for immediate contradiction
  
  if (trace_flag) print_trace(0,"starting to process input unit clauses");
  for(i=0;i<clauses.length;i++) {
    c=clauses[i];
    if (c.length!==1) continue;
    lit=c[0];
    if (lit<0) {s=-1; vn=0-lit;}
    else {s=1; vn=lit;}
    if (varvals[vn]!==0) {        
      if (varvals[vn]===s) continue; // have already        
      print_trace(0,"empty clause derived from "+clause_to_str(c));
      trace_list.push("Finished while preprocessing.");
      return [false,trace_list.join("\r\n")]; // immediate contradiction
    }      
    store_to_varvals(c[0],varvals);
    store_to_usable(c,usable_clauses);
  }  
  if (trace_flag) print_trace(0,"input unit clauses processed, starting to process non-unit");
  
  // second pass over all clauses sorts, preprocesses and stores non-unit clauses
  
  horn_flag=true; // clause set is horn if no clause contains more than one positive lit
  for(i=0;i<clauses.length;i++) {
    c=clauses[i];
    if (c.length<2) continue;    
    if (tautology(c)) continue;
    c=quick_sort_in_place(c);
    c=pre_preprocess_clause(c,varvals,[],tmp_array);
    if (c===false) {
      if (trace_flag) print_trace(0,"empty clause derived from "+clause_to_str(clauses[i]));
      trace_list.push("Finished while preprocessing.");
      return [false,trace_list.join("\r\n")]; // contradiction found
    }  
    if (c===true) continue; // subsumed
    store_to_usable(c,usable_clauses);
    if (horn_flag) { // no need to check if non-horn found before
      poscount=0;
      for(j=0;j<c.length;j++) {
        if (c[j]<0) continue;
        poscount++;
        if (poscount>1) {horn_flag=false; break;}  // found non-horn        
      }
    }
  }     
  if (trace_flag) {
    print_trace(0,"input non-unit clauses processed ");
    if (horn_flag) print_trace(0,"observation: clause set is horn");
    else print_trace(0,"observation: clause set is not horn");
  }        
  // prepare buckets of processed clauses by the first var
  // buckets where a var occurs positively
  posbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) posbuckets[i]=[];
  // buckets where a var occurs negatively
  negbuckets=new Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) negbuckets[i]=[];  
  
  // -------  main loop -----
  // runs until no more usable clauses: if this happens, clause set is satisfiable
  
  result=true; // unless made to false later
  while(selected=pick_selected(usable_clauses)) {
    if (trace_flag) print_trace(0,"selected candidate "+clause_to_str(selected));
    selected=preprocess_clause(selected,varvals,processed_clauses,posbuckets,negbuckets,tmp_array); 
    if (!selected) { result=false; break; }// contradiction found
    if (selected===true) { 
      if (trace_flag) print_trace(1,"subsumed");
      continue; // clause subsumed, pointless to use it
    }
    if (trace_flag) print_trace(0,"preprocessed to "+clause_to_str(selected)); 
    selected_clauses_count++;
    sl=selected[0]; // this and next nsl used for ordered resolution only
    if (sl<0) {nr=0-sl; sign=-1; bucket=posbuckets[nr];}
    else {nr=sl;sign=1; bucket=negbuckets[nr]; }
    nsl=0-sl;    
    // resolve all processed clauses with the selected clause
    for(p=0;p<bucket.length;p++) {
      processed=bucket[p];
      if (processed===true) continue; // we replace subsumed clauses with constant true
      if (trace_flag) print_trace(2,"processed "+clause_to_str(processed));
      generated_clauses_count++;
      derived=merge_rest(selected,processed,0,0,tmp_array,varvals);            
      if (derived===false) { result=false; break; } // contradiction found
      if (derived===true) {
        if (trace_flag) print_trace(4,"derived clause a tautology or subsumed");
        continue; // tautology or subsumed
      }              
      kept_clauses_count++;
      if (derived.length===1) store_to_varvals(derived[0],varvals);
      if (trace_flag) print_trace(4,"kept "+clause_to_str(derived));
      store_to_usable(derived,usable_clauses);
      // replace subsumed clauses with a constant true:
      if (ordered_subsumed(derived,processed)) bucket[p]=true;     
    }
    if (!result) break;
    // push the selected clause (removed from usable by now) to processed
    if (selected.length===1) store_to_varvals(selected[0],varvals);
    store_to_processed(selected,processed_clauses,posbuckets,negbuckets); 
  }
  
  // main loop ended

  txt="finished: selected clauses: "+selected_clauses_count;
  txt+=", generated clauses: "+generated_clauses_count;
  txt+=", kept clauses: "+kept_clauses_count;
  trace_list.push(txt);
  
  if (result) { 
    // copy derived units to a result_model (here this is only a partial model)
    result_model=[];
    for(i=0;i<varvals.length;i++) {
      if (varvals[i]!==0) result_model.push(showvar(i*varvals[i]));
    }
    if (result_model.length==0) result_model=true;
    return [result_model,trace_list.join("\r\n")];
  }  
  else {
    // contradiction found
    return [false,trace_list.join("\r\n")];  
  }    
}

/* Store single literal to an array of assigned variables:
   0 if not set, 1 if positive, -1 if negative
*/

function store_to_varvals(lit,varvals) {  
  if (lit<0) varvals[0-lit]=-1;
  else varvals[lit]=1;   
}

/* Store a clause to usable_clauses, assumed to be a list of sublists for
   each clause length 1,2,...,99 where 99 contains also all the longer clauses.
*/

function store_to_usable(clause,usable_clauses) {
  if (clause.length<100) usable_clauses[clause.length].push(clause);     
  else usable_clauses[99].push(clause); 
}

function store_to_processed(clause,processed_clauses,posbuckets,negbuckets) {
  var lit,bucket,nr;
  lit=clause[0];
  if (lit<0) negbuckets[0-lit].push(clause);
  else posbuckets[lit].push(clause); 
  processed_clauses.push(clause);
}
 
/* Return the first clause from the shortest non-empty bucket,
   removing the clause from the bucket.
*/

function pick_selected(usable_clauses) {
  var bucket,i;
  for(i=1;i<100;i++) {
    bucket=usable_clauses[i];
    if (bucket.length>0) return usable_clauses[i].shift(); // remove and return first el of bucket     
  }
  return false;
}

/* Return true if clause c is a tautology:
  c is a tautology iff it contains a variable positively and negatively  
*/

function tautology(c) {
  var i,j,l,nl; 
  for(i=1;i<c.length;i++) {
    l=c[i];
    nl=0-l;
    for(j=0;j<i;j++) {
      if (c[j]===nl) return true;
    }
  }
  return false; 
}  

/* Return true if clause c1 subsumes clause c2, false otherwise:
   assumes both c1 and c2 are ordered by literals, like [-3,-1,2,4].

  c1 subsumes c2 iff c1 is a subset of c2.  
*/

function ordered_subsumed(c1,c2) {
  var i,j,lit,found;
  if (c1.length>c2.length) return false;  
  j=0;
  // do all the c1 literals occur in c2?
  for (i=0;i<c1.length;i++) {
    lit=c1[i];    
    found=false;
    for(;j<c2.length && c2[j]<=lit; j++) { // assume the order
      if (c2[j]===lit) {found=true; j++; break; }      
    }
    if (!found) return false;
  }
  return true;
}  

/* Preprocessing a newly selected clause performs:
   - duplicate removal (only useful for initial clauses)
   - unit cutoffs and unit subsumption with assigned variables
   - full subsumption with processed clauses.
   Literals in the clause are assumed to be ordered, like [-3,-1,2,5]
  
  Return
    false: all literals were a cut off: contradiction found
    true: clause subsumed: do not use it
    clause: either unchanged or a shorter version, if some literals cut off
*/


function pre_preprocess_clause(clause,varvals,processed_clauses,tmp_array) {
  var j,i,lit,lastlit,s,vn,p,processed,k,found;
  j=0; // j will be the number of kept literals (rest will be cut using varvals)
  // check literals against already assigned variables
  lastlit=0;
  for(i=0;i<clause.length;i++) {
    lit=clause[i];
    if (lit==lastlit) continue;
    if (lit<0) {s=-1; vn=0-lit}
    else {s=1; vn=lit}
    if (varvals[vn]!==0) { // assigned-already vars either subsume clause or cut lit
      if (varvals[vn]===s) {        
        // do not subsume unit clauses with an assigned var during preprocessing
        if (clause.length>1) return true; // subsumed by the assigned var
        else tmp_array[j++]=lit; // here store only unit clauses for usage 
      } // notice we do not store a literal here if varvals[vn]!==s       
    } else {
      tmp_array[j++]=lit; // store for usage      
    }
    lastlit=lit;
  }
  // if all vars were cut, we found a contradiction
  if (j===0) return false;
  // check whether clause subsumed by some processed clause
  for(p=0;p<processed_clauses.length;p++) {
    processed=processed_clauses[p];
    if (processed.length<=j) { // j is the number of stored vars in tmp_array
      // check for subsumption, assuming literals in clauses are ordered
      k=0;
      for (i=0;i<processed.length;i++) {
        lit=processed[i];
        found=false;
        for(; k<j && tmp_array[k]<=lit; k++) { // assume the order
          if (tmp_array[k]===lit) {found=true; k++; break; }      
        }
        if (!found) break; // not subsumed
      }
      // all literals were found, hence subsumed
      if (found) return true;
    }
  }
  // clause was not subsumed: create a new copy only if some literals were cut
  if (j===clause.length) return clause;
  clause=new Int32Array(j);
  for(i=0;i<j;i++) clause[i]=tmp_array[i];
  return clause;    
}

function preprocess_clause(clause,varvals,processed_clauses,posbuckets,negbuckets,tmp_array) {
  var j,i,k,r,lit,lastlit,s,vn,p,processed,found,bucket;
  j=0; // j will be the number of kept literals (rest will be cut using varvals)
  // check literals against already assigned variables
  lastlit=0;
  for(i=0;i<clause.length;i++) {
    lit=clause[i];
    if (lit==lastlit) continue;
    if (lit<0) {s=-1; vn=0-lit}
    else {s=1; vn=lit}
    if (varvals[vn]!==0) { // assigned-already vars either subsume clause or cut lit
      if (varvals[vn]===s) {        
        // do not subsume unit clauses with an assigned var during preprocessing
        if (clause.length>1) return true; // subsumed by the assigned var
        else tmp_array[j++]=lit; // here store only unit clauses for usage 
      } // notice we do not store a literal here if varvals[vn]!==s       
    } else {
      tmp_array[j++]=lit; // store for usage      
    }
    lastlit=lit;
  }
  // if all vars were cut, we found a contradiction
  if (j===0) return false;
  // check whether clause subsumed by some processed clause
  for(r=0;r<j;r++) {
    lit=tmp_array[r];
    if(lit<0) {bucket=negbuckets[0-lit]; }
    else {bucket=posbuckets[lit]; }
    for(p=0;p<bucket.length;p++) {
      processed=bucket[p];
      if (processed.length<=j) { // j is the number of stored vars in tmp_array
        // check for subsumption, assuming literals in clauses are ordered
        k=0;
        for (i=0;i<processed.length;i++) {
          lit=processed[i];
          found=false;
          for(; k<j && tmp_array[k]<=lit; k++) { // assume the order
            if (tmp_array[k]===lit) {found=true; k++; break; }      
          }
          if (!found) break; // not subsumed
        }
        // all literals were found, hence subsumed
        if (found) return true;
      }
    }  
  }  
  /*
  for(p=0;p<processed_clauses.length;p++) {
    processed=processed_clauses[p];
    if (processed.length<=j) { // j is the number of stored vars in tmp_array
      // check for subsumption, assuming literals in clauses are ordered
      k=0;
      for (i=0;i<processed.length;i++) {
        lit=processed[i];
        found=false;
        for(; k<j && tmp_array[k]<=lit; k++) { // assume the order
          if (tmp_array[k]===lit) {found=true; k++; break; }      
        }
        if (!found) break; // not subsumed
      }
      // all literals were found, hence subsumed
      if (found) return true;
    }
  }
  */
  // clause was not subsumed: create a new copy only if some literals were cut
  if (j===clause.length) return clause;
  clause=new Int32Array(j);
  for(i=0;i<j;i++) clause[i]=tmp_array[i];
  return clause;    
}


    
/* Merge resolvents, eliminating vars which are cut off, checking for
  tautology, subsumption with assigned vars (unit clauses) and doing
  unit clause cutoff. Take:
  c1: first clause
  c2: second clause
  i1: cutoff literal index in c1
  i2: cutoff literal index in c1
  tmp_array: int32 array for temporarily collecting c2 vars
  varvals: assigned values for vars: values 0 (not assigned) or 1 or -1
  
  Return: either 
    false : empty clause (contradiction) derived
    true: either tautology or subsumed by a unit clause
    an int32 array of merged literals: if c1 and c2 are ordered (like [-3,-1,2,5]) 
      we preserve order in the merged array

  Examples where the first literals are cut:
  [1,2,3] and [-1,2,4] gives [2,3,4]
  [1,2,3] and [-1] gives [2,3]
  [1,2,3] and [-1,-1,4] gives [-1,2,3,4]
  [1,2,3] and [-1,1,4] gives [1,2,3,4]
*/

function merge_rest(c1,c2,i1,i2,tmp_array,varvals) {
  var c1len,c2varcount,i,j,p,l,nl,sn,lnr,res,rpos,found;
  // copy literals from c2 except i2 which are not in c1 to 
  // the temporary array tmp_array;
  // also check for tautology and do unit subsumption and cutoff
  // no need to loop over the first clause for tautology/unit checks.
  c1len=c1.length;
  c2varcount=0; // nr of literals in c2 which are merged to the result
  // loop over the second clause
  for (i=0;i<c2.length;i++) {
    if(i===i2) continue; // do not copy the cut literal
    l=c2[i]; // signed literal   
    nl=(0-l); // negated literal      
    if (l<0) { sn=-1; lnr=nl; }// sign and number of a literal
    else { sn=1; lnr=l; }
    if (varvals[lnr]!==0) {
      // variable is assigned already (due to a unit clause)
      if (varvals[lnr]===sn) return true; // result clause is subsumed by unit 
      // else the literal is cut off by unit, do not copy over to result
      continue;
    }      
    found=false;
    // check if var present in c1
    for(j=0;j<c1len;j++) {
      if (j===i1) continue; // var at i1 was cut off
      if (c1[j]===l) {found=true; break;} // already have this var
      if (c1[j]===nl) {return true; } // result clause is a tautology
    }
    if (!found) tmp_array[c2varcount++]=l; 
  }
  if (c2varcount===0 && c1len<2) return false; // empty clause derived        
  // make a fresh array res of a right size 
  res=new Int32Array((c1len-1)+c2varcount);
  // merge preserved c1 and c2 vars in the increasing order of size:
  // order helps in optimizing subsumption and resolution
  i=0; // loop over c1
  j=0; // loop over preserved c2 vars (tmp_array)
  p=0; // res array address for the next var to be stored
  while(i<c1len && j<c2varcount) { // merge c1 and c2 vars in right order
    if (i===i1) {i++; continue; } // do not copy the cut off literal
    if (c1[i]<=tmp_array[j]) res[p++]=c1[i++];
    else res[p++]=tmp_array[j++];    
  }
  for(;i<c1len;i++) { // copy rest from c1 except the cutoff literal
    if (i!==i1) res[p++]=c1[i];
  }
  for(;j<c2varcount;j++) res[p++]=tmp_array[j];  // copy rest of preserved c2 vars
  return res;
}


/* Stack-based in-place quicksort for int32array, taken from
   http://jsperf.com/int32-array-sort/2
*/

function quick_sort_in_place(arr) {
  var stack = [];
  var left = 0;
  var right = arr.length - 1;
  var i, j, swap, temp;
  while(true) {
    if(right - left <= 25){
      for(j=left+1; j<=right; j++) {
        swap = arr[j];
        i = j-1;
        while(i >= left && arr[i] > swap) {
          arr[i+1] = arr[i--];
        }
        arr[i+1] = swap;
      }
      if(stack.length == 0)    break;
      right = stack.pop();
      left = stack.pop();
    } else {
      var median = (left + right) >> 1;
      i = left + 1;
      j = right;
      swap = arr[median]; arr[median] = arr[i]; arr[i] = swap;
      if(arr[left] > arr[right]) {
        swap = arr[left]; arr[left] = arr[right]; arr[right] = swap;
      } if(arr[i] > arr[right]) {
        swap = arr[i]; arr[i] = arr[right]; arr[right] = swap;
      } if(arr[left] > arr[i]) {
        swap = arr[left]; arr[left] = arr[i]; arr[i] = swap;
      }
      temp = arr[i];
      while(true){
        do i++; while(arr[i] < temp);
        do j--; while(arr[j] > temp);
        if(j < i)    break;
        swap = arr[i]; arr[i] = arr[j]; arr[j] = swap;
      }
      arr[left + 1] = arr[j];
      arr[j] = temp;
      if(right - i + 1 >= j - left){
        stack.push(i);
        stack.push(right);
        right = j - 1;
      }else{
        stack.push(left);
        stack.push(j - 1);
        left = i;
      }
    }
  }
  return arr;
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

})(this.proplog_res = {});



