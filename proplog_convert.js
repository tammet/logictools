/* 
  Propositional logic formula and clause set converters and printers.

  The full set of exported functions and their usage:
  
    proplog_convert.parsed_print(["&",["&",["->","a",20],"a"],["-",20]], []) or
    proplog_convert.parsed_print([["-x", "y"],["x"],["y"]], []) for clauses
    proplog_convert.rename_vars_in_clauses([["-x", "y"],["x"],["y"]])
    proplog_convert.rename_vars_in_formula(["&",["&",["->","a",20],"a"],["-",20]])
    proplog_convert.formula_to_cnf(["&",["&",["->","a",20],"a"],["-",20]])
    proplog_convert.print_truthtable(["&",["&",["->","a",20],"a"],["-",20]]) or
    proplog_convert.print_truthtable([["-x", "y"],["x"],["y"]]) for clauses
   
  Fully self-contained, no dependencies.    
    
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

var maxvarnr=0; // used by the rename_vars_in_formula
var printlen=0; // used while printing
var printlst=[]; // used while printing
var printarray=[];  // used while printing the truth table  

// =========== formula and clause list printing ===============
  
  
 /*
  Print a parsed formula or a clause list: convert to text.  
  
  Takes:
    data - a formula like ["&",["&",["->","a",20],"a"],["-",20]] or
          a clause list like [[1,4,2],["-x",20],["x"],[["-",20]]]
    origvars - array containing for all vars in the frm the original var, like
      [null,"x",20]. If empty, variables in data area used directly.
  
  Returns a plaintext string for human reading.
*/  

exports.parsed_print = function(data,origvars) {   
  var tmp;
  tmp=typeof data;
  if (!data) return "";
  if (tmp==="number" || tmp==="string") return String(data);
  if (data.length<1) return "";
  if (typeof data[0]==="string") 
    return formula_print(data,origvars);
  else
    return clauses_print(data,origvars);
} 

function formula_print(data,origvars) {
  var tmp,res;
  printlst=[];
  printlen=0;
  formula_print_aux(data,origvars,0);
  res=printlst.join("");
  res=res.replace(/\"/g, ""); // remove "
  return res;
}


/* formula_print_aux pushes all printable strings to a list printlst
   and increases the length of printlen correspondingly. 

   These side effects are the only effects: no result returned.

  Takes:
    data - a formula like ["&",["&",["->","a",20],"a"],["-",20]] 
    origvars - array containing for all vars in the frm the original var, like
      [null,"x",20]. If empty, variables in data area used directly.
*/

function formula_print_aux(data,origvars,depth) {
  var tmp,nr,s,op,i;
  tmp=typeof data;
  if (!data) return;
  // first check if data is a literal
  if (tmp==="number") {
    nr=data;
    if (data<0) { 
      printlst.push("-"); 
      printlen++; 
      nr=0-data; 
    }    
    tmp=origvars[nr];
    if (tmp) { nr=tmp }
    s=String(nr);
    printlst.push(s); 
    printlen+=s.length;
    return;
  } else if (tmp==="string") {
    printlst.push(data);
    printlen+=data.length;
    return;
  }  
  // here data is a list
  if (data.length<2) return; // should not happen
  op=data[0];
  if (op==="-") {
    // negation op is printed as prefix and has only one argument
    printlst.push("-");
    printlen++;
    tmp=typeof data[1];
    //if (!(tmp==="string" || tmp==="number")) { printlst.push("("); printlen+=1; }
    formula_print_aux(data[1],origvars,depth+1);
    //if (!(tmp==="string" || tmp==="number")) { printlst.push(")"); printlen+=1; }    
  } else {
    // here ops are infix and may have many args
    // print surrounding ( ) only if not on top level
    if (depth>0) { printlst.push("("); printlen+=1; }
    for(i=1;i<data.length;i++) {
      formula_print_aux(data[i],origvars,depth+1);
      if (i<data.length-1) {
        printlst.push(" "+op+" ");
        printlen+=op.length+2;     
      }  
    }  
    if (depth>0) { printlst.push(")"); printlen+=1; }
  }
}
  
/* Converts a list of clauses to human-readable string.

   Takes:
    data - a clause list like [[1,4,2],["-x",20],["x"],[["-",20]]]
    origvars - array containing for all vars in the frm the original var, like
      [null,"x",20]. If empty, variables in data area used directly.

    Returns: a human-readable string in formula syntax, like
      (x V 4 V 20) &
      (-x v 20) &
      x &
      -20
*/

function clauses_print(data,origvars) {
  var i,j,c,lit,s,nr,sign,lit,tmp,res;
  printlst=[];
  printlen=0;
  for(i=0;i<data.length;i++) {
    c=data[i];    
    if (c.length!=1) {
      printlst.push("(");
      printlen++;
    }
    for(j=0;j<c.length;j++) {
      lit=c[j];
      sign="";
      tmp=typeof lit;
      if(tmp==="string") {
        s=String(lit);
      } else if (tmp==="number") {
        if (lit<0) {nr=0-lit; sign="-"; }
        else {nr=lit;}
        if (origvars[nr]) s=origvars[nr];
        else s=String(nr);
      } else if (lit[0]==="-") {
        s=lit[1];
        sign="-";
      }
      printlst.push(sign+s);
      printlen+=sign.length+s.length;
      if (j<c.length-1) {
        printlst.push(" V ");
        printlen+=3;
      }
    }
    if (j!=1) {
      printlst.push(")");
      printlen++;
    }
    if (i<data.length-1) {
      printlst.push(" & ");
      printlen+=3;
    }
    printlst.push("\n");
    printlen++;  
  }
  res=printlst.join("");
  res=res.replace(/\"/g, ""); // remove "
  return res;
}


// =========== variable renaming ===============
  
  
 /*
  Rename variables in a clause list so that variables are all integers and
  go 1,2,3,... without gaps. The clause list is destructively changed.
  
  Allows the input clause list to contain both
   - integer variables (like 3, -4: may be negative) and 
   - string variables (like "a1","-b": starting with - is considered 
     to mark a negative variable)
   - literals of the form ["-",var] where 
     var is a positive integer or a positive string var. 

  Assigns the original variables to renamed var keys in origvars array.
  
  Takes a clause list like [["-x",20],["x"],[["-",20]]]
  
  Returns a list of three elements  [count,clauses,orivars]:
    count  : number of variables in the new clause set like 2
    clauses : clauses containing renamed (integer) vars like
      [[-1,2],[1],[-2]]
    origvars : array containing for all vars in the new clauses the original var like
      [null,"x",20]
  
*/  

exports.rename_vars_in_clauses = function(clauses) {   
  var renamedvars={}, origvars=[];
  var i,j,clause,lit,nr,neg,count=0; 
  for (i=0; i<clauses.length; i++) {
    clause=clauses[i];        
    for (j=0; j<clause.length; j++) {
      lit=clause[j];
      neg=false;
      if (typeof lit === "string") {
        if (lit.lastIndexOf("-",0)===0) { nr=lit.substring(1); neg=true}
        else nr=lit;
      } else if (typeof lit === "number") {
        if (lit<0) { nr=0-lit; neg=true}
        else nr=lit;
      } else if (lit.length===2 && lit[0]==="-") {
        nr=lit[1];
        neg=true;
      } else {
        return [0,"error: not a clause list",[]];
      }
      if (! renamedvars[nr]) {
        count++;
        renamedvars[nr]=count;
        origvars[count]=nr;
        nr=count;
      } else {
        nr=renamedvars[nr];
      }
      if (neg) clause[j]=0-nr;
      else clause[j]=nr;
    }  
  }
  return [count,clauses,origvars];
}

 /*
  Rename variables in a parsed formula tree so that variables are all integers and
  go 1,2,3,... without gaps. The formula is destructively changed.  
  
  Allows the input clause set to contain both positive 
  integer variables and string variables (no negative ones: 
  all negative vars should be represented as terms ["-","x"]).

  Assigns the renamed variables to original variable keys 
  in renamedvars and the original variables to renamed in origvars.

  Takes a tree like ["&",["&",["->","a",20],"a"],["-",20]]      
  
  Returns a list of three elements  [count,tree,orivars]:
    count  : number of variables in the new tree, like 2
    tree : the modified tree containing renamed (integer) vars, 
      like ["&",["&",["->",1,20],1],["-",20]]
    origvars : array containing for all vars in the new tree the original var like
      [null,"a",20]
  
*/  

exports.rename_vars_in_formula = function(tree) {  
  var renamedvars={}, origvars=[];
  var res,tmp;     
  maxvarnr=0;  
  if (typeof tree==="number" || typeof tree==="string") {  
    // the tree is just a single variable 
    return [1,1,[0,tree]];
  } else {
    // any normal case: not just a single variable
    rename_vars_in_formula_aux(tree,origvars,renamedvars);  
    return [maxvarnr,tree,origvars];
  }  
}          

/* Destructively replaces string vars with integer vars,
   building up translation maps for both directions: origvars
   and renamedvars.

   tree is assumed to be a list.
*/

function rename_vars_in_formula_aux(tree,origvars,renamedvars) {
  var i,el,tmp;
  for(i=1;i<tree.length;i++) {
    // loop over all term arguments
    el=tree[i];
    tmp=typeof el;
    if (tmp==="number" || tmp==="string") {
      // el is a variable
      if (! renamedvars[el]) {
        maxvarnr++;
        renamedvars[el]=maxvarnr;
        origvars[maxvarnr]=el;
        tree[i]=maxvarnr;
      } else {
        tree[i]=renamedvars[el];
      }
    } else {  
      // el is a term
      rename_vars_in_formula_aux(el,origvars,renamedvars);
    }  
  }  
}



// ====== converter to CNF: clause normal form =======



 /*
  Convert a parsed formula tree to CNF: clause normal form.
  The original formula is preserved: the CNF form is built as a new
  structure.
  
  Allows the input clause set to contain both positive 
  and negative integer and string variables, plus the ["-",var] version
  for positive vars.

  Assigns the renamed variables to original variable keys 
  in renamedvars and the original variables to renamed in origvars.

  Takes a tree like ["&",["&",["->","a",20],"a"],["-",20]]      
  
  Returns a list of clauses like [[
  
*/  


exports.formula_to_cnf = function(frm) {   
  var pass1,pass2,tmp,res,i,c;  
  pass1=formula_negpush(frm,true);
  if (pass1==="error") return pass1;
  pass2=formula_cnf_distribute(pass1);
  // build clause lists
  tmp=typeof pass2;
  if (tmp==="string" || tmp==="number" || pass2[0]==="-") {
    return [[pass2]];
  } else if (pass2[0]==="V") {
    pass2.shift();
    return [pass2];
  } else {
    res=[];
    for (i=1;i<pass2.length;i++) {
      c=pass2[i];
      tmp=typeof c;
      if (tmp==="string" || tmp==="number" || c[0]==="-") {
        res.push([c]);
      } else {
        c.shift();
        res.push(c);
      }
    }
  }
  return res;
}

/* 
   Push negation in and convert 
     implication -> 
     equivalence <->
     xor +
   to disjunctions and conjunctions.

   Takes:
      frm: a tree like ["-",["&",["&",["->","a",2],"a"],["-",2]]]
      sign: true or false 

   Returns:
      a new tree containing only & and V and the negation pushed to variables.
*/

function formula_negpush(frm,sign) {
  var tmp,op,res,i;
  tmp=typeof frm;
  if (tmp==="number" || tmp==="string") {
    // frm is a variable
    if (sign) return frm; // no negation
    // must negate
    if (tmp==="number") return 0-frm;
    else if (tmp==="string" && frm.lastIndexOf("-",0)===0) return frm.substring(1);
    else return ["-",frm];  
  } else {  
    // frm is a term
    if (frm.length<2) return ["error","op must have some arguments"]; 
    op=frm[0];
    if (op==="-") {
      return formula_negpush(frm[1],!sign);
    } else if (op==="&" || op==="V") {
      if (sign) res=[op];
      else if (op==="&") res=["V"];
      else res=["&"];
      for (i=1;i<frm.length;i++) {
        res.push(formula_negpush(frm[i],sign));
      }
      return res;
    } else if (op==="->") {
      if (sign) res=["V"];
      else res=["&"];
      for(i=1;i<frm.length-1;i++) {
        res.push(formula_negpush(frm[i],!sign));
      }
      res.push(formula_negpush(frm[frm.length-1],sign));
      return res;
    } else if (op==="+") {
      if (frm.length!==3) return ["error","+ must have two arguments"]
      if (sign) {
        res=["V",["&",formula_negpush(frm[1],false),
                      formula_negpush(frm[2],true)],
                 ["&",formula_negpush(frm[1],true),
                      formula_negpush(frm[2],false)] ];
      } else {
        res=["V",["&",formula_negpush(frm[1],true),
                      formula_negpush(frm[2],true)],
                 ["&",formula_negpush(frm[1],false),
                      formula_negpush(frm[2],false)] ];        
      }
      return res;    
    } else if (op==="<->") {
      if (frm.length!==3) return ["error","<-> must have two arguments"]
      if (sign) {
        res=["&",["V",formula_negpush(frm[1],false),
                      formula_negpush(frm[2],true)],
                 ["V",formula_negpush(frm[1],true),
                      formula_negpush(frm[2],false)] ];
      } else {
        res=["V",["&",formula_negpush(frm[1],true),
                      formula_negpush(frm[2],false)],
                 ["&",formula_negpush(frm[1],false),
                      formula_negpush(frm[2],true)] ];        
      }
      return res;
    } else {
      // unknown op
      return "error";
    } 
  }    
}


/* 
  Convert formula to CNF (clause normal form) assuming
  formula has negation pushed to literals and contains
  otherwise only operators & and V.

  Essentially, each V is pushed inside so that all 
  V arguments are literals.

  Also, all & arguments in the result are either literals
  or disjunctions (V) of literals (i.e. nested &-s are
  flattened).

  Conversion uses only distribution laws: no new variables
  are introduced, tautologies are not removed nor any 
  other optimizations attempted.  
*/

function formula_cnf_distribute(frm) {
  var op,res,i,j,k,el,tmp,simp,comp;
  tmp=typeof frm;
  if (tmp==="number" || tmp==="string") {  
    // frm is a variable
    return frm;   
  } else {  
    // frm is a term
    op=frm[0];
    if (op==="-") return frm; // frm is a negative literal
    // here op is either & or V
    if (op==="&") {
      // conjunction
      res=["&"];
      for(j=1;j<frm.length;j++) {
        el=formula_cnf_distribute(frm[j]);
        tmp=typeof el;
        if (tmp==="number" || tmp==="string" || 
            el[0]==="-" || el[0]==="V") {
          res.push(el);
        } else {
          // flatten nested &-s
          for (k=1;k<el.length;k++) {
            res.push(el[k]);
          }
        }  
      }
      return res;      
    } else if (op==="V"){
      // disjunction
      simp=["V"]; // non-conjunctions only
      comp=[]; // list of conjunctions
      for(j=1;j<frm.length;j++) {
        el=formula_cnf_distribute(frm[j]);
        tmp=typeof el;
        if (tmp==="number" || tmp==="string" || el[0]==="-") {
          simp.push(el);
        } else if (el[0]==="&") {
          comp.push(el);
        } else {          
          for (k=1;k<el.length;k++) {
            simp.push(el[k]);
          }          
        }  
      }
      if (comp.length===0) return simp;      
      tmp=combinations(simp,comp);
      res=["&"];
      for(j=0;j<tmp.length;j++) {
        res.push(formula_cnf_distribute(tmp[j]));
      }        
      return res;
    } else {
      return ["error","op not allowed"];
    } 
  }  
}

/* Build all combinations of elements of lists in term,
   prepending all elements of pre to each result.
*/

function combinations(pre,terms) {
  var i,j,k,term,res,tmp,c;
  tmp=[pre];
  res=[];
  for(i=0;i<terms.length;i++) {
    term=terms[i];
    res=[];
    // make n versions of tmp, with each term[j] added
    for(j=1;j<term.length;j++) {
      // now make a copy of resultlists with term[j] added
      for(k=0;k<tmp.length;k++) {        
        c=tmp[k].slice(); // copy array
        c.push(term[j]);
        res.push(c);
      }  
    }
    tmp=res;    
  }
  return res;  
}


// ============ build the truth table ===================


exports.print_truthtable = function (data) {
  var tmp,count,frm,syntax,origvars,res;
  if (!data) return "";
  if (typeof data[0]==="number") {
    syntax="dpll";
    data.shift();
    tmp=exports.rename_vars_in_clauses(data);
  } else {
    syntax="formula";
    tmp=exports.rename_vars_in_formula(data);    
  }
  count=tmp[0];
  frm=tmp[1];
  origvars=tmp[2];
  res=truthtable(frm,syntax,count,origvars);
  return res;
}

function truthtable(frm,syntax,maxvarnr,origvars) {
  var rowcount,v,val,i,j,k,n,r,s,s2,frmstr,row;
  var varvals;
  var reslst,res;
  varvals=new Int32Array(maxvarnr+1);
  reslst=[];
  v=[];
  // make a special formula version with visual position at each op
  printlst=[]; // global used by add_print_pos_to_formula
  printlen=0;  // global used by add_print_pos_to_formula
  // frm is augmented with op poses
  if (syntax==="dpll") {
    frmstr="value";
    for(i=1;i<origvars.length;i++) origvars[i]=String(origvars[i]);
  } else {
    frm=add_print_pos_to_formula(frm,origvars,0); 
    frmstr=printlst.join(""); // printlst is just an ordinary printed frm
    frmstr=frmstr.replace(/\"/g, ""); // remove "
    printarray=[];
    for(i=0;i<frmstr.length;i++) printarray.push("&nbsp;"); // used for each rowprint
  }  
  // push varnames
  for(k=1;k<=maxvarnr;k++) v.push(origvars[k]);
  s=v.join(" ")+" | "+frmstr;
  reslst.push(s);
  // push horizontal line
  s2="";
  for(k=0;k<s.length;k++) s2+="&ndash;";
  reslst.push(s2);
  // push values to valuation lists and print
  rowcount=Math.pow(2,maxvarnr);
  if (rowcount>1024) 
    return "Table would contain "+rowcount+" rows: our printing limit is 1024 rows.";
  for(i=0;i<rowcount;i++) {
    v=[];
    n=i;
    for(j=1;j<=maxvarnr;j++) {      
      n=i>>>(maxvarnr-j);
      r=n%2;
      if (!r) varvals[j]=0;
      else varvals[j]=1;
      v.push(varvals[j]);
      s="";
      for(k=0;k<origvars[j].length;k++) s+="&nbsp;";
      v.push(s);
    }
    if (syntax=="dpll") {
      val=print_eval_dpll(frm,varvals);
      s=val;
    } else {
      val=print_eval_formula(frm,varvals,0);
      s=printarray.join("");
    }  
    v.push("&#124; ");
    v.push(s);
    reslst.push(v.join(""));
  }
  // print resulting table
  res=reslst.join("\n");
  return res;
}

/* print_eval_dpll checks whether a clause list contains a false
   clause under the valuation given in varvals.

   Vars in varvals must be all assigned either 0 or 1.
   Clauses must contain only integers.

   Returns 
    - "1" if no false clause found
    - "0" if a false clause is found
*/

function print_eval_dpll(lst,varvals) {
  var i,j,c,found,lit,nr,sign;  
  for(i=0;i<lst.length;i++) {
    c=lst[i];
    found=false;
    for(j=0;j<c.length;j++) {
      lit=c[j];
      if (lit<0) {nr=0-lit; sign=0; }
      else {nr=lit; sign=1; }
      if (varvals[nr]==sign) { found=true; break; }
    }
    if (!found) return "0";
  }
  return "1";
}

/* add_print_pos_to_formula is used for üreparing to
   print truth table rows: 
    - it pushes all printable strings to a list printlst 
      (to be used as an ordinary printed formula after join.(""))
    - increases the length of printlen correspondingly. 
    - returns the frm with each sublist led by operator augmented with an 
      integer indicating printing position: right after the operation.
   
  Takes:
    data - a formula like ["&",["&",["->","a",20],"a"],["-",20]] 
    origvars - array containing for all vars in the frm the original var, like
      [null,"x",20]. If empty, variables in data area used directly.
    depth - current depth in the formula tree
*/

function add_print_pos_to_formula(data,origvars,depth) {
  var tmp,nr,s,op,i,lst,oppos;
  tmp=typeof data;
  if (!data) return;
  // first check if data is a literal
  if (tmp==="number") {
    nr=data;
    if (data<0) { 
      printlst.push("-"); 
      printlen++; 
      nr=0-data; 
    }    
    tmp=origvars[nr];
    if (tmp) { nr=tmp }
    s=String(nr);
    printlst.push(s); 
    printlen+=s.length;
    return data;
  } else if (tmp==="string") {
    printlst.push(data);
    printlen+=data.length;
    return data;
  }  
  // here data is a list
  if (data.length<2) return null; // should not happen
  op=data[0];
  if (op==="-") {
    // negation op is printed as prefix and has only one argument
    printlst.push("-");
    oppos=printlen;
    printlen++;    
    tmp=typeof data[1];
    return ["-",oppos,add_print_pos_to_formula(data[1],origvars,depth+1)];
  } else {
    // here ops are infix and may have many args
    // print surrounding ( ) only if not on top level
    lst=[op,0];
    if (depth>0) { printlst.push("("); printlen+=1; }
    for(i=1;i<data.length;i++) {
      lst.push(add_print_pos_to_formula(data[i],origvars,depth+1));      
      if (i<data.length-1) {
        printlst.push(" "+op+" ");
        oppos=printlen+1;
        printlen+=op.length+2;     
      }
    }  
    if (depth>0) { printlst.push(")"); printlen+=1; }
    lst[1]=oppos;
    return lst;
  }
}


/* print_eval_formula is used for printing truth table rows:
   it computes the values of all operations in frm and inserts
   them to the positions in the printarray: positions are indicated
   by the position integer right after each op.

   Takes:
     frm - a special augmented formula built by add_print_pos_to_formula
     varvals - assignment array of vars (0: false, 1: true)
*/

function print_eval_formula(frm,varvals,depth) {  
  var op,oppos,j,tmp,tmp2,res;
  tmp=typeof frm;
  if (tmp==="number") return varvals[frm];
  op=frm[0];
  oppos=frm[1];
  if (op==="-") {
    tmp=print_eval_formula(frm[2],varvals,depth+1);
    if (tmp===1) res=0;
    else res=1;    
    printarray[oppos]=valfmt(res,depth);
    return res;
  } else if (op==="V") {
    res=0;
    for(j=2;j<frm.length;j++) {
      tmp=print_eval_formula(frm[j],varvals,depth+1);
      if (tmp===1) res=1;
    }
    printarray[oppos]=valfmt(res,depth);
    return res; 
  } else if (op==="&") {
    res=1;
    for(j=2;j<frm.length;j++) {
      tmp=print_eval_formula(frm[j],varvals,depth+1);
      if (tmp===0) res=0;
    }
    printarray[oppos]=valfmt(res,depth);
    return res; 
  } else if (op==="->") {
    res=0;
    for(j=2;j<frm.length-1;j++) {
      tmp=print_eval_formula(frm[j],varvals);
      if (tmp===0) res=1;
    }
    tmp=print_eval_formula(frm[frm.length-1],varvals,depth+1);
    if (tmp===1) res=1;
    printarray[oppos]=valfmt(res,depth);
    return res; 
  } else if (op==="<->") {
    res=1;
    tmp=print_eval_formula(frm[2],varvals,depth+1);
    for(j=3;j<frm.length;j++) {
      tmp2=print_eval_formula(frm[j],varvals,depth+1);
      if (tmp!==tmp2) res=0;
    }
    printarray[oppos]=valfmt(res,depth);
    return res; 
  } else if (op==="+") {
    tmp=print_eval_formula(frm[2],varvals,depth+1);
    tmp2=print_eval_formula(frm[3],varvals,depth+1);
    tmp=tmp+tmp2;
    if (tmp===1) res=1;
    else res=0;   
    printarray[oppos]=valfmt(res,depth);
    return res; 
  }
  return -1; // error: should not happen
}

function valfmt(s,depth) {
  if (depth>0) return String(s);
  else return "<b>"+String(s)+"</b>";
}

// ====== module end ==========

})(this.proplog_convert = {});



