/* Simple algorithms for converting and solving propositional formulas: 
   easy to hack and experiment with.

   See http://github.com/tammet/logictools

   Fully self-contained, no dependencies. Recommended to use together with the 
   proptools.html file providing a basic user interface for all the tools.
   
   Code is organized into several semi-independent sections. 
   The solver sections are independent of each other, but use globals, 
   the process trace printing functions and possibly some generic utils. 
   
   Sections and dependencies:
   
   * global variables: used by several sections below
   * top level: ui functions for calling parsers, solvers and printing to html
   * process trace printing: used by solver algorithms for process tracing
   * parsers: called only from the top level functions
   * converter to CNF: clause normal form converter, called only from the top level
   * problem generators: independent   
   * truth table solver: independent
   * naive resolution solver: independent
   * better resolution solver: independent
   * naive dpll solver: independent
   * better dpll solver: independent
  
  It is safe to completely remove any solver algorithm section you do not need: 
  the dpll_better in the last section is clearly the best solver algorithm here.
    
  This software is covered by the MIT licence http://en.wikipedia.org/wiki/MIT_License :

    Copyright (c) 2015 Tanel Tammet (tanel.tammet at gmail.com)

    Permission is hereby granted, free of charge, to any person obtaining a copy of 
    this software and associated documentation files (the "Software"), to deal in 
    the Software without restriction, including without limitation the rights to use,
    copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
    and to permit persons to whom the Software is furnished to do so, subject to the
    following conditions:

    The above copyright notice and this permission notice shall be included in all copies
    or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
    INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS 
    FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
    OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
    IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

// ====== global variables =========

// configuration for printing to html:

var process_html_id="process"; // output location in html
var result_html_id="result"; // output location in html
var start_time=0; // set by solver as it starts: used for printing to html

var trace_flag=false; // set by solver as it starts: false if no trace
var trace_method="console_trace"; // set by solver as it starts: selects console or html

// configuration for parsers:

var negchar="-"; // one-char string for negation in a formula syntax

//  used by several solvers:

var solver_algorithm; // algorithm selection string set in solve
var renamedvars={}; // set by rename_vars_in_clauses
var origvars=[]; // set by rename_vars_in_clauses
var result_model=[]; // set by solver to a resulting model: values of vars
  
// statistical counts:
  
var unit_propagations_count=0; // used by the dpll solver
var units_derived_count=0; // used by the dpll solver  
var pure_derived_count=0; // used by the dpll solver
var max_depth_count=0; // used by the dpll solver 
var truth_value_leaves_count=0;   // used by the dpll and table solvers
var truth_value_calc_count=0; // used by the table solvers
var selected_clauses_count=0; // used by the resolution solvers
var generated_clauses_count=0; // used by the resolution solvers
var kept_clauses_count=0; // used by the resolution solvers
  
// ====== top level: calling and printing from/to html =====

/* Top level table solver functions: called from html with a text input.
   Runs the selected solver algorithm, printing the process and result to html.
*/
  
function solve(txt,algorithm,trace) {
  solver_algorithm=algorithm; // store to global var
  trace_method=trace; // store to global var
  if (!trace_method || trace_method=="no_trace") trace_flag=false;
  else trace_flag=true;  
  clear_output(); // we need to wait a bit after that
  // avoid doing html dom change in parallel to solving
  window.setTimeout(function(){solve_aux(txt)},100);
}  
  
function solve_aux(txt) {
  // naive/better is differentiated by the algorithm check later in solve_...
  if (solver_algorithm=="dpll_better") solve_by_dpll(txt);
  else if (solver_algorithm=="dpll_naive") solve_by_dpll(txt);
  else if (solver_algorithm=="truth_table_naive") solve_by_table(txt);
  else if (solver_algorithm=="truth_table_better") solve_by_table(txt);      
  else if (solver_algorithm=="resolution_naive") solve_by_resolution(txt);
  else if (solver_algorithm=="resolution_better") solve_by_resolution(txt);  
  else show_process("algorithm not implemented");  
}  

function solve_by_table(txt) {
  var tmp,maxvar,clauses,i,res,txt;
  start_time=new Date().getTime();  
  show_process("starting to parse");    
  clauses=parse_dimacs(txt); 
  // return first el and change clauses by removing the first el: 
  maxvar=clauses.shift();   
  show_process("there are "+clauses.length+" clauses, max variable nr is "+maxvar);
  res=satisfiable_by_table(clauses,maxvar) // actual solver called 
  txt="finished: evaluations count is "+truth_value_calc_count;
  txt+=", leaves count is "+truth_value_leaves_count;
  show_process(txt);
  if (res) {
    // output to html
    txt="Clause set is satisfiable: there is a model ";
    for(i=0;i<result_model.length;i++) txt+=result_model[i]+" ";    
    show_result(txt);  
  } else {
    // output to html
    show_result("Clause set is not satisfiable: no model exists.");  
  }    
}  

function solve_by_resolution(txt) {
  var tmp,maxvar,clauses,i,res,txt,stats,res;
  start_time=new Date().getTime();  
  show_process("starting to parse");
  clauses=parse_dimacs(txt);  
  // return first el and change clauses by removing the first el: 
  maxvar=clauses.shift();   
  show_process("got "+clauses.length+" clauses, max var "+maxvar);
  if (solver_algorithm=="resolution_naive") 
    res=resolution_naive(clauses,maxvar); // actual solver called
  else
    res=resolution_better(clauses,maxvar); // actual solver called
  // output to html
  stats="selected clauses: "+selected_clauses_count;
  stats+=", generated clauses: "+generated_clauses_count;
  stats+=", kept clauses: "+kept_clauses_count;
  txt="finished: "+stats;
  show_process(txt);
  if (res) {
    txt="Clause set is satisfiable: there is a model. A partial model is: "; 
    for(i=0;i<result_model.length;i++) txt+=result_model[i]+" ";    
    show_result(txt);           
  } else {
    show_result("Clause set is not satisfiable: no model exists.");  
  }    
}  

function solve_by_dpll(txt) {
  var tmp,maxvar,clauses,i,res,txt,stats,res;
  start_time=new Date().getTime();  
  show_process("starting to parse");
  clauses=parse_dimacs(txt);  
  // return first el and change clauses by removing the first el: 
  maxvar=clauses.shift();   
  show_process("got "+clauses.length+" clauses, max var "+maxvar);
  if (solver_algorithm=="dpll_naive") 
    res=dpll_naive(clauses,maxvar); // actual solver called
  else
    res=dpll_better(clauses,maxvar); // actual solver called
  // output to html
  txt="finished: unit propagations count is "+unit_propagations_count;
  txt+=", units derived count is "+units_derived_count; 
  txt+=", pure literal count is "+pure_derived_count;
  txt+=", max depth is "+max_depth_count;   
  show_process(txt);
  if (res) {
    txt="Clause set is satisfiable: there is a model. A partial model is: ";     
    for(i=0;i<result_model.length;i++) txt+=result_model[i]+" ";    
    show_result(txt);         
  } else {
    show_result("Clause set is not satisfiable: no model exists.");  
  }    
}  

// ====== process trace printing  ==========

/* show_process ... clear_output are utilities for printing to html

*/

function show_process(txt) {
  append_to_place("<div>"+passed_time()+": "+txt+"</div>",process_html_id);
}

function print_trace(depth,txt) {
  var i,s="";
  if (trace_flag && trace_method=="console_trace") {
    for(i=0;i<depth;i++) s+=" ";
    console.log(s+txt);
  } else if (trace_flag && trace_method=="html_trace") {    
    for(i=0;i<depth;i++) s+="&nbsp;";
    append_to_place("<div><tt>"+s+"</tt>"+txt+"</div>",process_html_id);
  }  
}

function clause_to_str(cl) {
  var i,s="";
  if (cl===true) return "tautology";
  if (!cl) return "empty";
  for(i=0;i<cl.length;i++) s+=cl[i]+" ";
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

function show_result(txt) {
  append_to_place(txt,result_html_id);
}

function passed_time() {
  var now=new Date().getTime();  
  var passed=String(now-start_time);
  if ((passed.length)===0) passed="000";
  else if ((passed.length)===1) passed="00"+passed;
  else if ((passed.length)===2) passed="0"+passed;
  return passed;
}

function append_to_place(txt,placeid) {
  var place=document.getElementById(placeid);
  var newcontent=document.createElement('div');
  newcontent.innerHTML=txt;
  while (newcontent.firstChild) {
    place.appendChild(newcontent.firstChild);
  } 
}

function clear_output() {
  var place=document.getElementById(process_html_id);
  place.innerHTML="";   
  place=document.getElementById(result_html_id);
  place.innerHTML=""; 
}

function formula_to_txt(f) {
  return JSON.stringify(f);
}


// ====== parsers ==========

/* Parse dimacs format string and return a list where 
  - first el is the maximal variable nr (always positive)
  - from the second el start clauses like [[1,-2],[-2,1]] 
  for example: [2,[1,-2],[-2,1]]  

  We parse a superset of dimacs, where
  - c and p lines may be missing altogether
  - textual variable names like var7 may be used in addition to numeric variable names
  - 0 at end may be missing

  Standard dimacs formula example:

  c start with comments
  p cnf 5 3
  1 -5 4 0
  -1 5 3 4 0
  -3 -4 0

  We allow also the following form of the previous example:
  
  x -5 4 
  -x 5 y 4
  -y -4 
*/  
  
function parse_dimacs(txt) {
  var clauses,clause,lines,line,spl,i,j,sv,nv,anv,maxv;
  clauses=[];
  maxv=0;
  lines=txt.split("\n");
  for(i=0;i<lines.length;i++) {
    line=lines[i].trim();
    if (!line || line.charAt(0)==="c" || line.charAt(0)==="p") continue;
    clause=[]; 
    spl=line.split(" ");
    for(j=0;j<spl.length;j++) {
      sv=spl[j];
      if (!sv) continue;
      nv=parseInt(sv);
      if (isNaN(nv)) continue;
      if (nv===0) break;
      anv=nv;
      if (anv<0) anv=anv * -1;
      if (anv>maxv) maxv=anv;
      clause.push(nv);
    }
    if (clause) clauses.push(clause);
  }
  clauses.unshift(maxv); // prepend to clause list
  return clauses;
}  

/* Parse a non-clausal formula in the traditional infix notation like

  ** NOT FINISHED **
*/


function parse_formula(txt) {
  var tmp,exp,pos;  
  tmp=parse_expression_tree(txt,0);
  exp=tmp[0];
  pos=tmp[1];
  tmp=parse_skip(txt,pos);
  if (tmp<txt.length) return(parse_error("some text remains after formula ends"));
  return exp;
} 

function parse_expression_tree(txt,pos) {
  var isneg,exp,op,node;
  pos=parse_skip(txt,pos);
  isneg=false;
  if (parse_isatpos(txt,pos,"-")) { isneg=true; pos++;}
  else if (parse_isatpos(txt,pos,"~")) { isneg=true; pos++;}
  console.log("pet isneg "+isneg+" pos "+pos);
  tmp=parse_factor_tree(txt,pos);
  console.log("pet tmp "+tmp+" pos "+pos);
  exp=tmp[0];
  pos=tmp[1];
  if (isneg) exp=["-",exp];
  pos=parse_skip(txt,pos);  
  while(true) {
    console.log("loop starts pos "+pos);
    op=null;
    if (parse_isatpos(txt,pos,"&")===true) { op="&"; pos++; } 
    else if (parse_isatpos(txt,pos,"|")===true) { op="|"; pos++; }
    else if (parse_isatpos(txt,pos,"v")===true) { op="|"; pos++; }
    else if (parse_isatpos(txt,pos,"V")===true) { op="|"; pos++; }
    else if (parse_isatpos(txt,pos,"->")===true) { op="->"; pos+=2; }
    else if (parse_isatpos(txt,pos,"=>")===true) { op="->"; pos+=2; }
    else if (parse_isatpos(txt,pos,"<->")===true) { op="<->"; pos+=3; }
    else if (parse_isatpos(txt,pos,"<=>")===true) { op="<->"; pos+=3; }
    if (op===null) break;
    console.log("op "+op+" pos "+pos);
    tmp=parse_term_tree(txt,pos);    
    console.log("tmp "+JSON.stringify(tmp))
    exp=[op,exp,tmp[0]];
    pos=tmp[1];
    console.log("exp "+JSON.stringify(exp))
    pos=parse_skip(txt,pos);
    console.log("pos "+pos);
    if (pos>=txt.length) break;    
  }
  return [exp,pos];
} 


function parse_term_tree(txt,pos) {
  var c,n,j,v,tmp,exp;
  console.log("pftr called pos "+pos);
  pos=parse_skip(txt,pos);
  console.log("pftr after skip pos "+pos);
  j=pos;
  found=false;
  v=null;
  while(true) {
    c=txt.charAt(j);
    n=txt.charCodeAt(j);
    // numbers and letters
    if (j<txt.length && ((n>=48 && n<=57) || (n>=65 && n<=122))) { j++; continue; } 
    // not a number or a letter or at the end of text
    console.log("pftr pos"+pos+" j "+j);
    if (j>pos) {
      // a var was found
      v=txt.substring(pos,j);
      console.log("pftr v "+v);
      return [v,j];
    }
    break;
  }  
  if (c==="(") {
    pos++;
    tmp=parse_expression_tree(txt,pos);
    console.log("pftr tmp "+JSON.stringify(tmp));
    exp=tmp[0];
    pos=tmp[1];    
    pos=parse_skip(txt,pos);
    if (txt.charAt(pos)!==")") return(parse_error("right parenthesis missing"));
    pos++;
    return[exp,pos];
  } else if (c===")") {
    return(parse_error("extra right parenthesis"));
  } else {
    return(parse_error("unexpected text ..."+c+"... encountered"));
  }
}

function parse_isatpos(txt,pos,str) {
  if(str.length===1) {
    if(txt.charAt(pos)===str) return true;
    else return false;
  } else {
    if(txt.substr(pos,str.length)===str) return true;
    else return false;
  }
}

function parse_skip(txt,pos) {
  var c;
  while(pos<txt.length) {    
    c=txt.charAt(pos); 
    if (c===" " || c==="\t" || c==="\n" || c==="\r") pos++;
    else break;
  }
  return pos;
}

function parse_error(txt) {
  console.log(txt);
  return txt;
}

  
/*
  Rename variables in a clause set so that variables are all integers and
  go 1,2,3,... without gaps. Allows the input clause set to contain both
  integer variables and string variables (in the latter case negative ones
  start with -). Assigns the renamed variables to original variable keys 
  in the global object renamedvars and the original variables to renamed in the
  global array origvars. Returns the maximal new variable found.  
  
*/  

function rename_vars_in_clauses(clauses) {   
  // globals set: renamedvars, origvars;
  var i,j,clause,nr,neg,count=0; 
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];        
    for (j=0; i<clause.length; j++) {
      neg=false;
      if (typeof clause[j] === "string") {
        if (clause[j].charAt(0)===negchar) { nr=substr(clause[j],1); neg=true}
        else nr=clause[j];
      } else {
        if (clause[j]<0) { nr=clause[j] * -1; neg=true}
        else nr=clause[j];
      }  
      if (! renamedvars.hasOwnProperty(nr)) {
        count++;
        renamedvars[nr]=count;
        origvars[count]=nr;
      }
      if (neg) clause[j]=nr * -1;
      else clause[j]=nr;
    }  
  }
  return count;
}

// ====== converter to CNF: clause normal form =======

// TODO

// ====== problem generators =====

/* Use the selected algorithm and convert generated clauses to text: 
   called from html. Take
    n: number of distinct variables in the generated clause set, as text
    algorithm: algorithm name as text
*/

function generate_problem(n,algorithm) {
  var n,clauses,res;
  // parse and check n
  if (!n) return "";
  n=parseInt(n);
  if (isNaN(n)) return "";  
  // call the selected algorithm
  if (algorithm==="all_combinations") {
    clauses=prop_combinations_problem(n);
  } else if (algorithm==="small_unsat") {
    clauses=prop_small_unsat_problem(n);
  } else if (algorithm==="random_3-sat") {
    clauses=prop_random_3_sat_problem(n);  
  } else {
    clauses=[];
  }  
  // convert to text
  res="";
  for (i=0;i<clauses.length;i++) {
    res=res+clauses[i].join(" ")+"\n"; 
  }
  return res;
}

/* Generate all combinations of vars 1,..,n both
  positively and negatively: guaranteed to be
  unsatisfiable and non-horn. 
  Example for 2 as clauses: [[1,2],[1,-2],[-1,2],[-1,-2]]  
*/  

function prop_combinations_problem(n) {
  var tmp,tmp1,tmp2,res;
  if (n<0) return [];
  if (n==1) return [[1],[-1]];
  tmp=prop_combinations_problem(n-1);
  res=[]
  for(i=0;i<tmp.length;i++) { 
    tmp1=tmp[i].slice(); // copy array
    tmp1.push(n); // append n
    res.push(tmp1); 
    tmp2=tmp[i].slice(); // copy array
    tmp2.push(0-n); // append -n
    res.push(tmp2);     
  }
  return res;
}  

/* Generate a small unsatisfiable problem 
   Example for 3: [[1,2,3],[-1],[-2],[-3]]
*/ 

function prop_small_unsat_problem(n) {
  var res,clause,i;
  res=[];
  clause=[];
  for (i=1;i<=n;i++) clause.push(i);
  res.push(clause);
  for (i=1;i<=n;i++) res.push([0-i]);
  return res;
}

/* Generate a small random 3-sat problem
   Example for 3: [[-3,1,2],[1,-2],...,[1,2,3]]
   where number of clauses is set below in nr=n*...
*/ 

function prop_random_3_sat_problem(n) {
  var res,clause,nr,i,j,r1,r2,s,v,ok;    
  if (n<2) return [];
  // see the discussion of the ratio 4 in the classic
  // http://www.aaai.org/Papers/AAAI/1992/AAAI92-071.pdf :
  // 4 is the integer closest to the "hardest" ratio
  nr=n*4; // how many 3-element clauses
  
  res=[];  
  for(i=0;i<nr;i++) {
    clause=[];
    for(j=0;j<3;j++) {
      r1=Math.random();
      if (r1<0.5) s=0-1;
      else s=1;
      r2=Math.random();
      v=Math.floor((r2*n)+1);
      if (clause.indexOf(s*v)<0) {             
        clause.push(s*v);
      }        
    }
    res.push(clause);
  }  
  return res;
}


// ====== truth table solver  ==========

/* 
  Check whether a clause set is satisfiable, by search through the truth
  value table: checking out all possible valuations of variables.
  Take 
    clauses: a clause set (array of arrays) like [[1,-2],[-2,1]] 
    maxvarnr: the maximal variable in clauses (integer) like 2.
  Return 
    true iff the clause set is satisfiable (ie there is an assignment
      of values to vars so that the clause set is evaluated to true). 
    false iff the clause set is contradictory (like [[1],[-1]])
*/

function satisfiable_by_table(clauses,maxvarnr) {
  var i,varvals,j;
  // zero statistics counters
  truth_value_calc_count=0; 
  truth_value_leaves_count=0; 
  result_model=[];
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);    
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;  
  if (satisfiable_by_table_at(clauses,varvals,1,1,1) || 
      satisfiable_by_table_at(clauses,varvals,1,-1,1)) {    
    return true;
  }
  return false;
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
  if (trace_flag) print_trace(depth,"setting var "+varnr+" to "+val);
  if (solver_algorithm==="truth_table_better" || varnr===varvals.length-1) {    
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
    //show_process("i "+i+" "+i*varvals[i]);
    if (varvals[i]!==0) result_model.push(i*varvals[i]);
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


// ====== naive resolution solver ==========

/* Full resolution search for contradiction. Takes:
    clauses: list of clauses like [[1],[3,-1,-2],[-3]]
    maxvarnr: number of the largest variable (3 for the example above)

    Uses a given-clause algorithm and does not use any optimisations, 
    except the forward subsumption check of a selected usable clause 
    with all processed clauses (this should guarantee termination of the search,
    given enough time and space).

    The only globals used are for statistics: 
    selected_clauses_count, generated_clauses_count, kept_clauses_count.

    Returns
      true: clause set is satisfiable
      false: clause set is contradictory

*/

function resolution_naive(clauses,maxvarnr) {
  var usable_clauses, processed_clauses, selected, processed;
  var tmp_array;
  var p,found,i,j,sl,nsl,derived;
  // zero statistics
  selected_clauses_count=0; 
  generated_clauses_count=0;
  kept_clauses_count=0;
  // prepare working arrays
  processed_clauses=[]; 
  usable_clauses=clauses;  
  tmp_array=new Int32Array(maxvarnr*2+1); // used during clause merge
  // main loop runs until no more usable clauses: if this happens, clause set is satisfiable
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
            if (derived===false) return false; // contradiction found
            if (derived===true) continue; // tautology
            kept_clauses_count++;
            usable_clauses.push(derived);                                    
          }          
        }
      }
    }
    // push the selected clause (removed from usable by now) to processed
    processed_clauses.push(selected);
  }
  return true; // cannot derive anything more: clause set is satisfiable
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
  var varcount,num,c,pos,i,j,l,nl,res;
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

// ====== better resolution solver ==========

/* Full resolution search for contradiction. Takes:
    clauses: list of clauses like [[1],[3,-1,-2],[-3]]
    maxvarnr: number of the largest variable (3 for the example above)

    Uses a given-clause algorithm and several optimisations:
    - preprocessing clauses
    - unit resolution in case the clause set is horn (max one positive lit per clause)
    - always selecting the shortest usable clause as given
    - storing and simplification by unit clauses (assigned variables)
    - forward subsumption of selected clauses and partial backward-subsumption
    - literals in clauses are ordered like [-3-1,2,5]    

    The only globals used are for statistics: 
    selected_clauses_count, generated_clauses_count, kept_clauses_count.

    Returns
      true: clause set is satisfiable
      false: clause set is contradictory

*/

function resolution_better(clauses,maxvarnr) {
  var usable_clauses, processed_clauses, selected, processed; 
  var tmp_array, var_vals;
  var i,j,c,lit,s,vn,p,sl,nsl,derived,kept,l,horn_flag;
  // zero statistics
  selected_clauses_count=0; 
  generated_clauses_count=0;
  kept_clauses_count=0;
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
    if (lit<0) {s=0-1; vn=0-lit;}
    else {s=1; vn=lit;}
    if (varvals[vn]!==0) {        
      if (varvals[vn]===s) continue; // have already        
      print_trace(0,"empty clause derived from "+clause_to_str(c));
      return false; // immediate contradiction
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
    c=preprocess_clause(c,varvals,[],tmp_array);
    if (c===false) {
      if (trace_flag) print_trace(0,"empty clause derived from "+clause_to_str(clauses[i]));
      return false; // contradiction found
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
    if (horn_flag) print_trace(0,"clause set is horn");
    else print_trace(0,"clause set is not horn");
  }        
  
  // -------  main loop -----
  // runs until no more usable clauses: if this happens, clause set is satisfiable
  
  while(selected=pick_selected(usable_clauses)) {
    print_trace(0,"selected "+clause_to_str(selected));
    selected=preprocess_clause(selected,varvals,processed_clauses,tmp_array);       
    if (!selected) return false; // contradiction found
    if (selected===true) { 
      if (trace_flag) print_trace(1,"subsumed");
      continue; // clause subsumed, pointless to use it
    }
    print_trace(0,"preprocessed to "+clause_to_str(selected)); 
    selected_clauses_count++;
    // resolve all processed clauses with the selected clause
    for(p=0;p<processed_clauses.length;p++) {
      processed=processed_clauses[p];
      if (processed===true) continue; // we replace subsumed clauses with constant true
      if (trace_flag) print_trace(2,"processed "+clause_to_str(processed));
      // only unit resolution allowed if the clause set is horn
      if (horn_flag && selected.length>1 && processed.length>1) continue; 
      // do all resolution steps for selected and processed
      for(i=0;i<selected.length;i++) {
        sl=selected[i];
        nsl=0-sl;
        for(j=0;j<processed.length;j++) {
          if (processed[j]>nsl) break; // assume literals in clauses are ordered
          if (nsl===processed[j]) {
            generated_clauses_count++;
            derived=merge_rest(selected,processed,i,j,tmp_array,varvals);            
            if (derived===false) return false; // contradiction found
            if (derived===true) {
              if (trace_flag) print_trace(4,"derived clause a tautology or subsumed");
              continue; // tautology or subsumed
            }              
            kept_clauses_count++;
            if (derived.length===1) store_to_varvals(derived[0],varvals);
            if (trace_flag) print_trace(4,"kept "+clause_to_str(derived));
            store_to_usable(derived,usable_clauses);
            // replace subsumed clauses with a constant true:
            if (ordered_subsumed(derived,processed)) processed_clauses[p]=true;                           
          }          
        }
      }
    }
    // push the selected clause (removed from usable by now) to processed
    if (selected.length===1) store_to_varvals(selected[0],varvals);
    processed_clauses.push(selected);
  }
  
  // main loop ended
  
  print_trace(0,"returning true");
  // copy derived units to a result_model (here this is only a partial model)
  result_model=[];
  for(i=0;i<varvals.length;i++) {
    if (varvals[i]!==0) result_model.push(i*varvals[i]);
  }  
  return true; // cannot derive anything more: clause set is satisfiable
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
 
/* Return the first clause from the shortest non-empty bucket,
   removing the clause from the bucket.
*/

function pick_selected(usable_clauses) {
  var bucket,i;
  for(i=1;i<100;i++) {
    bucket=usable_clauses[i];
    if (bucket.length>0) return bucket.shift(); // remove and return first el of bucket     
  }
  return false;
}

/* Return true if clause c is a tautology:
  c is a tautology iff it contains a variable positively and negatively  
*/

function tautology(c) {
  var i,l,nl; 
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
  
function preprocess_clause(clause,varvals,processed_clauses,tmp_array) {
  var j,i,lit,lastlit,s,vn,p,processed,k,found;
  j=0; // j will be the number of kept literals (rest will be cut using varvals)
  // check literals against already assigned variables
  lastlit=0;
  for(i=0;i<clause.length;i++) {
    lit=clause[i];
    if (lit==lastlit) continue;
    if (lit<0) {s=0-1; vn=0-lit}
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
  var c1len,c2varcount,i,j,l,nl,lnr,res,rpos;
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
    if (l<0) { sn=0-1; lnr=nl; }// sign and number of a literal
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

// ========== naive dpll solver ==========

/* 
  Check whether a clause set is satisfiable, using a naive implementation 
  of the dpll (Davis-Putnam-Logemann-Loveland) procedure combining truth
  table search with the resolution-like unit propagation.

  The standard pure-literal rule is not implemented in this naive version, 
  since it is not really crucial for the algorithm.
  
  The code is very similar to the pure table solver, except we use
  a unit-propagating, derived-varlist-returing naive_dpll_satisfiable_at
  instead of the satisfiable_by_table_at.
  
  Take 
    clauses: a clause set (array of arrays) like [[1,-2],[-2,1]] 
    maxvarnr: the maximal variable in clauses (integer) like 2.
  Return 
    true iff the clause set is satisfiable (ie there is an assignment
      of values to vars so that the clause set is evaluated to true). 
    false iff the clause set is contradictory (like [[1],[-1]])
*/

function dpll_naive(clauses,maxvarnr) {
  var i,j,res,varvals;
  // zero statistics globals
  unit_propagations_count=0; 
  truth_value_leaves_count=0; 
  units_derived_count=0; 
  pure_derived_count=0; // not used in dpll_naive
  max_depth_count=0;
  result_model=[];
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;
  // no variable assigned here: dpll_satisfiable_at 
  // unit-propagates and then selects an unassigned variable to split
  res=naive_dpll_satisfiable_at(clauses,varvals,0,0,0);
  return res;
}


function naive_dpll_satisfiable_at(clauses,varvals,varnr,val,depth) {
  var propres,i,nextvar,sign,errtxt;
  if (depth>max_depth_count) max_depth_count=depth; // statistics
  // functions ok without passing a variable to assign (if varnr==0)
  if (varnr!==0) {
    // assigned variable passed
    if (trace_flag) print_trace(depth,"setting var "+varnr+" to "+val);
    varvals[varnr]=val; 
    if (varnr===varvals.length-1) truth_value_leaves_count++;
  } else {
    if (trace_flag) print_trace(depth,"search called without setting a var before");
  }
  // call unit propagation
  propres=naive_unit_propagate(clauses,varvals,depth);
  if (propres===1) { naive_dpll_store_model(varvals); varvals[varnr]=0; return true;}
  // if result false (-1) naive_unit_propagate restores the varvals state itself
  if (propres===-1){ varvals[varnr]=0; return false;} 
  // find next unassigned var to split
  nextvar=0;
  for(i=1;i<varvals.length;i++) {
    if (varvals[i]===0) { nextvar=i; break; }
  }  
  if (nextvar!==0) {
    if (trace_flag) print_trace(depth,"splitting variable "+nextvar);
    if (naive_dpll_satisfiable_at(clauses,varvals,nextvar,1,depth+1) ||
        naive_dpll_satisfiable_at(clauses,varvals,nextvar,-1,depth+1)) {
      // not necessary to restore split var: search is halted anyway                    
      return true;
    }   
    varvals[nextvar]=0; // restore split var
    for(i=0;i<propres.length;i++) varvals[propres[i]]=0; // restore derived vars
    return false;        
  } else {
    // error case: should not happen
    errtxt="Error in the naive_dpll_satisfiable_at";
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

function naive_unit_propagate(clauses,varvals,depth) {
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
    allclausesfound=true;
    derived_queue=[]; // derived units (literals) during one iteration 
    for (i=0; i<clauses.length; i++) {
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
      if (clauseval!==1) {
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
      }      
      if (unassigned_count!==0) allclausesfound=false;
    }
    if (allclausesfound) {
      // all clauses were subsumed or all the variables in all clauses had a value
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
        if (trace_flag) derived_units_txt+=lit+" ";
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

function naive_dpll_store_model(varvals) {
  var i;
  //result_model=[];
  for(i=1;i<varvals.length;i++) {
    // store assigned values as -1, 3, -4, ...
    //show_process("i "+i+" "+i*varvals[i]);
    if (varvals[i]!==0) result_model.push(i*varvals[i]);
  }  
}

// ====== improved dpll solver ==========

/* 
  Check whether a clause set is satisfiable, using an implementation 
  of the dpll (Davis-Putnam-Logemann-Loveland) procedure combining truth
  table search with the resolution-like unit propagation.

  This algorithm uses (in addition to the methods in the naive version):
  - pure literal rule
  - weighted selection of the next variable to split
  - derived variables in unit propagation used immediately

  The code is very similar to the pure table solver, except we use
  a unit-propagating, derived-varlist-returing naive_dpll_satisfiable_at
  instead of the satisfiable_by_table_at.

  See http://minisat.se/downloads/MiniSat.pdf for a good introduction
  to optimizing propositional solvers.

  Take 
    clauses: a clause set (array of arrays) like [[1,-2],[-2,1]] 
    maxvarnr: the maximal variable in clauses (integer) like 2.
  Return 
    true iff the clause set is satisfiable (ie there is an assignment
      of values to vars so that the clause set is evaluated to true). 
    false iff the clause set is contradictory (like [[1],[-1]])
*/

function dpll_better(clauses,maxvarnr) {
  var i,j,res,varvals,occvars;
  // zero statistics globals
  unit_propagations_count=0; 
  truth_value_leaves_count=0; 
  units_derived_count=0; 
  pure_derived_count=0;
  max_depth_count=0;
  result_model=[];
  // variable values are 0 if not set, 1 if positive, -1 if negative
  varvals=new Int32Array(maxvarnr+1);
  for(i=0;i<=maxvarnr;i++) varvals[i]=0;
  // temporary array used for finding the next variable to split
  occvars=new Int32Array(maxvarnr+1);
  // no variable assigned here: dpll_satisfiable_at 
  // unit-propagates and then selects an unassigned variable to split
  res=dpll_satisfiable_at(clauses,varvals,0,0,0,occvars);
  return res;
}


function dpll_satisfiable_at(clauses,varvals,varnr,val,depth,occvars) {
  var propres,nextvar,sign,errtxt;
  if (depth>max_depth_count) max_depth_count=depth; // statistics
  // functions without passing a variable to assign (then varnr==0)
  if (varnr!==0) {
    // assigned variable passed
    if (trace_flag) print_trace(depth,"setting var "+varnr+" to "+val);
    varvals[varnr]=val; 
    if (varnr===varvals.length-1) truth_value_leaves_count++;
  } else {
    if (trace_flag) print_trace(depth,"search called without setting a var before");
  }
  // call unit propagation
  propres=unit_propagate(clauses,varvals,depth);
  if (propres===1) { dpll_store_model(varvals); return true;}
  // if result false (-1) unit_propagate restores the varvals state itself
  if (propres===-1){ varvals[varnr]=0; return false;} 
  // find next unassigned var to split
  nextvar=dpll_next_var(clauses,varvals,occvars);
  if ((typeof nextvar) !== "number") {
    // pure literal found
    pure_derived_count++;
    nextvar=nextvar[0]; // literal was encoded into a single-element array
    if (nextvar<0) {nextvar=0-nextvar; sign=0-1; }
    else { sign=1; }
    if (trace_flag) print_trace(depth,"pure variable "+nextvar+", sign "+sign);
    if (dpll_satisfiable_at(clauses,varvals,nextvar,sign,depth+1,occvars)) {
      // not necessary to restore: search is halted anyway    
      return true;
    }   
    varvals[nextvar]=0; // restore assigned pure var
    for(i=0;i<propres.length;i++) varvals[propres[i]]=0; // restore derived vars
    return false;
  } else if (nextvar!==0) {
    // normal variable found
    if (trace_flag) print_trace(depth,"splitting variable "+nextvar);
    if (dpll_satisfiable_at(clauses,varvals,nextvar,1,depth+1,occvars) ||
        dpll_satisfiable_at(clauses,varvals,nextvar,-1,depth+1,occvars)) {
      // not necessary to restore: search is halted anyway     
      return true;
    }   
    varvals[nextvar]=0; // restore split var
    for(i=0;i<propres.length;i++) varvals[propres[i]]=0; // restore derived vars
    return false;        
  } else {
    // error case: should not happen
    errtxt="Error in the dpll_satisfiable_at";
    console.log(errtxt);
    show_process(errtxt);
  }
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


function unit_propagate(clauses,varvals,depth) {
  var i,j,lit,nr,vval,polarity;
  var clause,clauseval,unassigned_count,unassigned_lit,allvarsfound,allclausesfound;
  var derived_vars,derived_flag,derived_units_txt;
  unit_propagations_count++;  
  derived_vars=[]; // all vars with a value derived in the forthcoming main loop
  derived_units_txt=""; // used only for the trace: all the derived literals (signed vars)  
  // the main loop is run, deriving new unit clauses, until either:
  // - the clause set is detected to be unsatisfiable
  // - the clause set is detected to be satisfiable
  // - there are no more derived unit clauses
  while(true) {
    allclausesfound=true;
    derived_flag=false; // were there derived units (literals) during one iteration?
    for (i=0; i<clauses.length; i++) { // iterate over clauses      
      clause=clauses[i];        
      clauseval=0;
      unassigned_count=0; // count unassigned vars in clause
      unassigned_lit=0; // 0 means no unassigned vars found for this clause
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
      if (clauseval!==1) {
        // clause is not subsumed by varvals
        if (unassigned_count===0) {
          if (trace_flag) print_trace(depth,"value is false");
          for(j=0;j<derived_vars.length;j++) varvals[derived_vars[j]]=0; // restore derived
          return -1;
        } else if (unassigned_count===1) {
          // unassigned_lit is a derived literal
          units_derived_count++;
          derived_flag=true;
          if (unassigned_lit<0) {nr=0-unassigned_lit; polarity=-1}
          else {nr=unassigned_lit; polarity=1};
          varvals[nr]=polarity;
          derived_vars.push(nr);
          if (trace_flag) derived_units_txt+=unassigned_lit+" ";
        }        
      }      
      if (unassigned_count!==0) allclausesfound=false;
    }
    if (allclausesfound) {
      // all clauses were subsumed or all the variables in all clauses had a value
      if (trace_flag) print_trace(depth,"value is true");
      // no need to restore: whole search finished
      //for(j=0;j<derived_vars.length;j++) varvals[derived_vars[j]]=0; // restore derived
      return 1;
    }
    // in case there are any derived units present, iterate the main loop
    if (!derived_flag) break; // nothing derived, terminate loop
    // else some units were derived: iterate the main loop    
  }
  // main loop ended
  if (trace_flag) {
    print_trace(depth,"value is undetermined");
    if (derived_vars.length>0) print_trace(depth,"derived units "+derived_units_txt);
  }    
  return derived_vars;
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

function dpll_next_var(clauses,varvals,occvars) {
  var i,j,lit,nr,vval,oval,polarity,bonus;
  var clause,clen,blen;
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
  for(i=1;i<occvars.length;i++) {
    oval=occvars[i];
    if (oval===0) continue;
    if (oval<2 && varvals[i]===0) return [oval*i]; // pure literal is returned as a signed single-el list
    if (oval>bonus && varvals[i]===0) {bonus=oval; nr=i;}    
  } 
  // var with max bonus  
  if (nr<0) return 0-nr;
  else if (nr>0) return nr;
  else {
    for(i=1;i<varvals.length;i++) if(varvals[i]===0) return i;
  }
}


/* 
  Store the current valuation of variables to be printed out later as a model.
*/

function dpll_store_model(varvals) {
  var i;
  //result_model=[];
  for(i=1;i<varvals.length;i++) {
    // store assigned values as -1, 3, -4, ...
    //show_process("i "+i+" "+i*varvals[i]);
    if (varvals[i]!==0) result_model.push(i*varvals[i]);
  }  
}



// ====== the end ==========





