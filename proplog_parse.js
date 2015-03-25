/* 
  Propositional logic formula and clause set (dimacs) syntax parsers.

  Use like this: 
    proplog_parse.parse("-1 2\n 1 \n -2")  parses both dimacs and formulas
    proplog_parse.parse_tree("-1 2\n 1 \n -2") returns parse result as a string
    proplog_parse.parse_dimacs("-1 2\n 1 \n -2")
    proplog_parse.parse_formula("x=>y & x & -y")
   
  Fully self-contained, no dependencies.     
  Exports functions 
    parse
    parse_tree
    parse_dimacs
    parse_formula
        
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

 
// ====== universal parser ==========

/* parse tries to first interpret input as dimacs text,
   if this fails, it tries to parse input as a formula.
  
   Input: 
     - txt: plain text in dimacs or formula syntax
  
   Returns one of:
     - parsed dimacs as [2,[-1,2],[1],[-2]] (first el is nr of vars)
     - parsed formula as ["&",["->","a","b"],"b"]] 
     - formula parsing error as ["error",some_err_string]

*/  
  
exports.parse = function(txt) {
  var tmp;  
  tmp=exports.parse_dimacs(txt);
  if (tmp[0]!==0 && tmp.length>1) {
    // possibly dimacs
    if (tmp[1].length>0) return tmp;
  }  
  // here we assume non-dimacs, parse as formula
  tmp=exports.parse_formula(txt);
  return tmp;
}  


/* parse_tree returns a human-readable parse result string
   built by stringifying the result of parse_formula.
   & and V operators are added to dimacs parse results.
*/

exports.parse_tree = function(txt) {
  var tmp,i,res;  
  
  tmp=exports.parse(txt);
  if (err_data(tmp)) 
    return ("syntax error: "+tmp[1]);
  else if (typeof tmp[0]=="number") {
    // dimacs: add & and V operators
    res=["&"];
    for(i=1;i<tmp.length;i++) {     
      if (tmp[i].length>1) res.push(["V"].concat(tmp[i]));
      else if (tmp[i].length===1) res.push(tmp[i][0]);
    }
    return JSON.stringify(res);
  } else {
    // formula    
    return JSON.stringify(tmp);
  }  
} 
    
/* ============ 
  
  Parse dimacs format string and return a list where 
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
  ===============
*/  
  
exports.parse_dimacs = function(txt) {
  var clauses,clause,lines,line,spl,i,j,sv,nv,anv,maxv;
  clauses=[];
  maxv=0;
  lines=txt.split("\n");
  for(i=0;i<lines.length;i++) {
    line=lines[i].trim();
    if (!line || line.lastIndexOf("c",0)===0 || line.lastIndexOf("p",0)===0) continue;
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

/* =========================

  Parse a non-clausal formula in the traditional infix notation like

  (a & -b) -> c
  
  where 

    negation symbols are -, ~ : - is used in the constructed term
    conjunction symbols are &,and: & is used in the constructed term
    disjunction symbols are |,v,V,or : V is used in the constructed term
    xor symbols are +,xor : + is used in the constructed term
    implication symbols are ->,=> : -> is used in the constructed term
    equivalence symbols are <->,<=> : <-> is used in the constructed term

  There is no operator precedence: all operators are bound from left:
    a & b v c & d v e 
    is parsed as
    [V,[&,[V,[&,a,b],c],d],e]

  ========================= 
*/


/* parse_formula returns a parse tree as a nested list like
  
  ["&",["-","a"],"b"]

  In the error case it returns

  ["error", concrete_error_message_string]

*/

exports.parse_formula = function(txt) {
  var tmp,exp,pos;  

  tmp=parse_expression_tree(txt,0);
  if (err_data(tmp)) return tmp;
  exp=tmp[0];
  pos=tmp[1];
  tmp=parse_skip(txt,pos);
  if (tmp<txt.length) 
    return (parse_error("remaining text at "+txt.substring(pos)));
  else
    return exp;
} 

function parse_expression_tree(txt,pos) {
  var isneg,exp,op,node,tmp;
  pos=parse_skip(txt,pos);
  isneg=false;
  if (parse_isatpos(txt,pos,"-")) { isneg=true; pos++;}
  else if (parse_isatpos(txt,pos,"~")) { isneg=true; pos++;}
  tmp=parse_term_tree(txt,pos);
  if (err_data(tmp)) return tmp;
  exp=tmp[0];
  pos=tmp[1];
  if (isneg) exp=["-",exp];
  pos=parse_skip(txt,pos);  
  while(true) {
    op=null;
    if (parse_isatpos(txt,pos,"&")===true) { op="&"; pos++; } 
    else if (parse_isatpos(txt,pos,"and")===true) { op="&"; pos+=3; }
    else if (parse_isatpos(txt,pos,"+")===true) { op="+"; pos++; }
    else if (parse_isatpos(txt,pos,"xor")===true) { op="+"; pos+=3; }
    else if (parse_isatpos(txt,pos,"|")===true) { op="V"; pos++; }
    else if (parse_isatpos(txt,pos,"v")===true) { op="V"; pos++; }
    else if (parse_isatpos(txt,pos,"V")===true) { op="V"; pos++; }
    else if (parse_isatpos(txt,pos,"or")===true) { op="V"; pos+=3; }
    else if (parse_isatpos(txt,pos,"->")===true) { op="->"; pos+=2; }
    else if (parse_isatpos(txt,pos,"=>")===true) { op="->"; pos+=2; }
    else if (parse_isatpos(txt,pos,"<->")===true) { op="<->"; pos+=3; }
    else if (parse_isatpos(txt,pos,"<=>")===true) { op="<->"; pos+=3; }
    if (op===null) break;
    tmp=parse_term_tree(txt,pos);
    if (err_data(tmp)) return tmp;    
    exp=[op,exp,tmp[0]];
    pos=tmp[1];
    pos=parse_skip(txt,pos);
    if (pos>=txt.length) break;    
  }
  return [exp,pos];
} 


function parse_term_tree(txt,pos) {
  var c,n,j,v,tmp,exp,found,isneg;
  pos=parse_skip(txt,pos); 
  isneg=false;
  if (parse_isatpos(txt,pos,"-")) { isneg=true; pos++; pos=parse_skip(txt,pos); }
  else if (parse_isatpos(txt,pos,"~")) { isneg=true; pos++; pos=parse_skip(txt,pos); }   
  j=pos;
  found=false;
  v=null;
  while(true) {
    c=txt.charAt(j);
    n=txt.charCodeAt(j);
    // numbers and letters
    if (j<txt.length && ((n>=48 && n<=57) || (n>=65 && n<=122))) { j++; continue; } 
    // not a number or a letter or at the end of text
    if (j>pos) {
      // a var was found
      v=txt.substring(pos,j);
      if (isneg) return [["-",v],j];
      return [v,j];
    }
    break;
  }  
  if (c==="(") {
    pos++;
    tmp=parse_expression_tree(txt,pos);
    if (err_data(tmp)) return tmp;
    exp=tmp[0];
    pos=tmp[1];    
    pos=parse_skip(txt,pos);
    if (txt.charAt(pos)!==")") 
      return(parse_error("right parenthesis missing"));
    pos++;
    if (isneg) return [["-",exp],pos];
    return[exp,pos];
  } else if (c===")") {
    return(parse_error("extra right parenthesis at "+txt.substring(pos)));
  } else {
    return(parse_error("unexpected text "+c+" encountered at "+txt.substring(pos)));
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
  return ["error",txt];
}

function err_data(data) {
  if (typeof data!== "string" && data[0]==="error") return true;
  else return false;
}

// ====== module end ==========

})(this.proplog_parse = {});



