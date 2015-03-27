/* 
  Top level UI layer for several proposition logic solvers, parsers and converters,
  easy to hack and experiment with.     
  
  Use like this: proplog_ui.solve("-1 2\n 1 \n -2","dpll_better","html")
  
  Exports functions:
    solve
    build
    clear_output
    show_syntax
  
  Load these javascript files before running the functions in the current module:
  
    proplog_parse.js
    proplog_convert.js
    proplog_generate.js
    proplog_dpll.js
    proplog_naivedpll.js
    proplog_res.js
    proplog_naiveres.js
    proplog_searchtable.js
    
  See http://logictools.org and http://github.com/tammet/logictools 
  for full UI and tools.
  
  Recommended to use with the accompanying proplog.html file providing 
  a basic user interface and other tools for propositional logic.           
  
  This software is covered by the MIT licence, see http://opensource.org/licenses/MIT
  or http://en.wikipedia.org/wiki/MIT_License
  
  Copyright (c) 2015 Tanel Tammet (tanel.tammet at gmail.com)  
*/  


(function(exports) {
  "use strict";
// ====== module start =========
 
// configuration for printing to html:

var process_html_id="process"; // output location in html
var result_html_id="result"; // output location in html
var syntax_html_id="syntax"; // syntax description location in html

// set by solver as it starts: used for printing to html
  
var start_time=0; 

// ====== top level: calling and printing from/to html =====

/* Top level table solver functions: called from html with a text input.
   Runs the selected solver algorithm, printing the process and result to html.
  
  Takes:
    txt - the propositional problem in DIMACS or formula syntax
    solver_algorithm - one of "dpll_better","dpll_naive",
      "truth_table_naive","truth_table_better","resolution_naive","resolution_better"
    trace_method - one of "none", "html", "text", "console"
  
  Does:
    - calls parsers and converters on the input txt
    - runs the selected prover on the parsed and converted txt
    - injects trace and results to the html page
*/

exports.solve = function (txt,solver_algorithm,trace_method) {
  exports.clear_output(); // we need to wait a bit after that
  // avoid doing html dom change in parallel to solving
  window.setTimeout(function(){solve_aux(txt,solver_algorithm,trace_method)},100);
}  

function solve_aux(txt,solver_algorithm,trace_method) {
  var parsed,converted,maxvar,clauses,origvars,i,res,txt,stats,res;
  start_time=new Date().getTime();  
  show_process("starting to parse");
  parsed=proplog_parse.parse(txt);
  origvars=[];  
  if (typeof parsed[0]=="number") {
    // dimacs
    show_process("parsed, detected dimacs syntax");
    clauses=parsed;
    maxvar=clauses.shift();
  } else if (parsed[0]==="error") {
    // err
    show_process("Syntax error: "+parsed[0]);
    show_result("Syntax error: "+parsed[0]);
    return;
  } else {
    // formula
    show_process("parsed, detected formula syntax");
    converted=proplog_convert.formula_to_cnf(parsed); 
    converted=proplog_convert.rename_vars_in_clauses(converted); 
    maxvar=converted[0];
    clauses=converted[1];
    origvars=converted[2];
  }
  // return first el and change clauses by removing the first el: 
  show_process("got "+clauses.length+" clauses, max var "+maxvar);
  
  if (solver_algorithm=="dpll_better") 
    res=proplog_dpll.dpll(clauses,maxvar,trace_method,origvars);
  if (solver_algorithm=="dpll_old") 
    res=proplog_olddpll.olddpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="dpll_naive")    
    res=proplog_naivedpll.naivedpll(clauses,maxvar,trace_method,origvars);
  else if (solver_algorithm=="truth_table_naive") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"leaves",trace_method,origvars); 
  else if (solver_algorithm=="truth_table_better") 
    res=proplog_searchtable.searchtable(clauses,maxvar,"nodes",trace_method,origvars); 
  if (solver_algorithm=="resolution_naive") 
    res=proplog_naiveres.naiveres(clauses,maxvar,trace_method,origvars); 
  else if (solver_algorithm=="resolution_better")
    res=proplog_res.resolution(clauses,maxvar,trace_method,origvars); 
  
  show_process(res[1]);
  
  if (res[0]!==false) {                 
    if (solver_algorithm=="resolution_naive" || solver_algorithm=="resolution_better") {    
      txt="Clause set is <b>true</b> for some assignment of values to variables."; 
      // resolution generates no model or partial model
      if (res[0]!=true && res[0].length>0) {
        txt+=" A partial suitable assignment is: ";
        for(i=0;i<res[0].length;i++) txt+=res[0][i]+" ";    
        show_result(txt);         
      } else {
        show_result(txt);
      }
    } else {
      // other methods typically generate a model
      txt="Clause set is <b>true</b> if we assign values to variables as: "; 
      for(i=0;i<res[0].length;i++) txt+=res[0][i]+" "; 
      show_result(txt);
    }      
  } else {
    // clause set unsatisfiable
    show_result("Clause set is <b>false</b> for all possible assignments to variables.");  
  }   
}  

/* Top level truth table and normal form builders.
  
  Takes:
    txt - the propositional problem in DIMACS or formula syntax
    build_select - one of "truth_table","CNF",
  
  Does:
    - calls parsers and converters on the input txt
    - builds the required result
    - injects the result to the html page
*/


exports.build = function (txt,build_select) {
  exports.clear_output(); // we need to wait a bit after that
  // avoid doing html dom change in parallel to building
  window.setTimeout(function(){build_aux(txt,build_select)},100);
}

function build_aux(txt,build_select) {
  var res;
  start_time=new Date().getTime();  
  show_process("starting to parse");
  if (!txt) {
    show_result("No input.");
    return;
  }
  res=proplog_parse.parse(txt);
  //show_process("parsing finished");
  if (res[0]==="error") {
    show_result("Parse error: "+res[1]);
    return;
  }
  if (build_select=="parse_tree") {
    if (typeof res[0]==="number") {
      show_process("parsed, detected dimacs syntax");
      res.shift();
    } else {
      show_process("parsed, detected formula syntax");
    }
    res=JSON.stringify(res);
    res=res.replace(/"/g,"")
    //res=proplog_convert.parsed_print(res,[]);    
  } else if (build_select=="truth_table") {
    if (typeof res[0]==="number") {
      show_process("parsed, detected dimacs syntax");
    } else {
      show_process("parsed, detected formula syntax");
    }  
    res=proplog_convert.print_truthtable(res);
  } else if (build_select=="cnf") {    
    if (typeof res[0]==="number") {
      show_process("parsed, detected dimacs syntax");
      res.shift();
      res=proplog_convert.parsed_print(res,[]);      
    } else {
      show_process("detected formula syntax");
      res=proplog_convert.formula_to_cnf(res);
      res=proplog_convert.parsed_print(res,[]);
    }
  }
  show_process("finished");
  //show_result("<pre>"+res+"</pre>");  
  show_result("<tt>"+res.replace(/\n/g,"<br>")+"</tt>");  
}  


/* clear_output ... are utilities for printing to html

*/

exports.clear_output = function() {
  var place=document.getElementById(process_html_id);
  place.innerHTML="";   
  place=document.getElementById(result_html_id);
  place.innerHTML=""; 
}

function show_process(txt) {
  append_to_place("<div>"+passed_time()+": "+txt+"</div>",process_html_id);
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


// ====== module end ==========

})(this.proplog_ui = {});



