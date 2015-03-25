/* 
  Propositional logic problem generator for simple types of problems.

  Use like this: proplog_generate.generate_problem(3,"all_combinations")
   
  Fully self-contained, no dependencies.   
  Exports function generate_problem.  
    
  See http://logictools.org and http://github.com/tammet/logictools 
  for UI and other tools.
  
  Recommended to use with the accompanying proplog.html file providing 
  a basic user interface and other tools for propositional logic.           
  
  This software is covered by the MIT licence, see http://opensource.org/licenses/MIT
  or http://en.wikipedia.org/wiki/MIT_License
  
  Copyright (c) 2015 Tanel Tammet (tanel.tammet at gmail.com)    
*/



(function(exports) {
  "use strict";
// ====== module start =========

 
// ====== problem generators =====

/* Use the selected algorithm and convert generated clauses to text: 
   called from html. Take
    n: number of distinct variables in the generated clause set, as text
    algorithm: algorithm name as text
*/

exports.generate_problem = function (n,algorithm) {
  var clauses,res,i;
  
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
  var tmp,tmp1,tmp2,res,i;
  if (n<0) return [];
  if (n==1) return [[1],[-1]];
  tmp=prop_combinations_problem(n-1);
  res=[];
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

// ====== module end ==========

})(this.proplog_generate = {});



