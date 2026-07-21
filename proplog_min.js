(function(exports){"use strict";var process_html_id="process";var result_html_id="result";var syntax_html_id="syntax";var start_time=0;exports.solve=function(txt,solver_algorithm,trace_method){exports.clear_output();window.setTimeout(function(){solve_aux(txt,solver_algorithm,trace_method)},100);}
function solve_aux(txt,solver_algorithm,trace_method){var parsed,converted,maxvar,clauses,origvars,i,res,txt,stats,res;start_time=new Date().getTime();show_process("starting to parse");parsed=proplog_parse.parse(txt);origvars=[];if(typeof parsed[0]=="number"){show_process("parsed, detected dimacs syntax");clauses=parsed;maxvar=clauses.shift();}else if(parsed[0]==="error"){show_process("Syntax error: "+parsed[0]);show_result("Syntax error: "+parsed[0]);return;}else{show_process("parsed, detected formula syntax");converted=proplog_convert.formula_to_cnf(parsed);converted=proplog_convert.rename_vars_in_clauses(converted);maxvar=converted[0];clauses=converted[1];origvars=converted[2];}
show_process("got "+clauses.length+" clauses, max var "+maxvar);if(solver_algorithm=="cdcl")
res=proplog_cdcl.cdcl(clauses,maxvar,trace_method,origvars);else if(solver_algorithm=="dpll_better")
res=proplog_dpll.dpll(clauses,maxvar,trace_method,origvars);else if(solver_algorithm=="dpll_old")
res=proplog_olddpll.olddpll(clauses,maxvar,trace_method,origvars);else if(solver_algorithm=="dpll_naive")
res=proplog_naivedpll.naivedpll(clauses,maxvar,trace_method,origvars);else if(solver_algorithm=="truth_table_naive")
res=proplog_searchtable.searchtable(clauses,maxvar,"leaves",trace_method,origvars);else if(solver_algorithm=="truth_table_better")
res=proplog_searchtable.searchtable(clauses,maxvar,"nodes",trace_method,origvars);else if(solver_algorithm=="resolution_naive")
res=proplog_naiveres.naiveres(clauses,maxvar,trace_method,origvars);else if(solver_algorithm=="resolution_better")
res=proplog_res.resolution(clauses,maxvar,trace_method,origvars);show_process(res[1]);if(res[0]!==false){if(solver_algorithm=="resolution_naive"||solver_algorithm=="resolution_better"){txt="Clause set is <b>true</b> for some assignment of values to variables.";if(res[0]!=true&&res[0].length>0){txt+=" A partial suitable assignment is: ";for(i=0;i<res[0].length;i++)txt+=res[0][i]+" ";show_result(txt);}else{show_result(txt);}}else{txt="Clause set is <b>true</b> if we assign values to variables as: ";for(i=0;i<res[0].length;i++)txt+=res[0][i]+" ";show_result(txt);}}else{show_result("Clause set is <b>false</b> for all possible assignments to variables.");}}
exports.build=function(txt,build_select){exports.clear_output();window.setTimeout(function(){build_aux(txt,build_select)},100);}
function build_aux(txt,build_select){var res;start_time=new Date().getTime();show_process("starting to parse");if(!txt){show_result("No input.");return;}
res=proplog_parse.parse(txt);if(res[0]==="error"){show_result("Parse error: "+res[1]);return;}
if(build_select=="parse_tree"){if(typeof res[0]==="number"){show_process("parsed, detected dimacs syntax");res.shift();}else{show_process("parsed, detected formula syntax");}
res=JSON.stringify(res);res=res.replace(/"/g,"")}else if(build_select=="truth_table"){if(typeof res[0]==="number"){show_process("parsed, detected dimacs syntax");}else{show_process("parsed, detected formula syntax");}
res=proplog_convert.print_truthtable(res);}else if(build_select=="cnf"){if(typeof res[0]==="number"){show_process("parsed, detected dimacs syntax");res.shift();res=proplog_convert.parsed_print(res,[]);}else{show_process("detected formula syntax");res=proplog_convert.formula_to_cnf(res);res=proplog_convert.parsed_print(res,[]);}}
show_process("finished");show_result("<tt>"+res.replace(/\n/g,"<br>")+"</tt>");}
exports.clear_output=function(){var place=document.getElementById(process_html_id);place.innerHTML="";place=document.getElementById(result_html_id);place.innerHTML="";}
function show_process(txt){append_to_place("<div>"+passed_time()+": "+txt+"</div>",process_html_id);}
function show_result(txt){append_to_place(txt,result_html_id);}
function passed_time(){var now=new Date().getTime();var passed=String(now-start_time);if((passed.length)===0)passed="000";else if((passed.length)===1)passed="00"+passed;else if((passed.length)===2)passed="0"+passed;return passed;}
function append_to_place(txt,placeid){var place=document.getElementById(placeid);var newcontent=document.createElement('div');newcontent.innerHTML=txt;while(newcontent.firstChild){place.appendChild(newcontent.firstChild);}}})(this.proplog_ui={});
(function(exports){"use strict";exports.parse=function(txt){var tmp;tmp=exports.parse_dimacs(txt);if(tmp[0]!==0&&tmp.length>1){if(tmp[1].length>0)return tmp;}
tmp=exports.parse_formula(txt);return tmp;}
exports.parse_tree=function(txt){var tmp,i,res;tmp=exports.parse(txt);if(err_data(tmp))
return("syntax error: "+tmp[1]);else if(typeof tmp[0]=="number"){res=["&"];for(i=1;i<tmp.length;i++){if(tmp[i].length>1)res.push(["V"].concat(tmp[i]));else if(tmp[i].length===1)res.push(tmp[i][0]);}
return JSON.stringify(res);}else{return JSON.stringify(tmp);}}
exports.parse_dimacs=function(txt){var clauses,clause,lines,line,spl,i,j,sv,nv,anv,maxv;clauses=[];maxv=0;lines=txt.split("\n");for(i=0;i<lines.length;i++){line=lines[i].trim();if(!line||line.lastIndexOf("c",0)===0||line.lastIndexOf("p",0)===0)continue;clause=[];spl=line.split(" ");for(j=0;j<spl.length;j++){sv=spl[j];if(!sv)continue;nv=parseInt(sv);if(isNaN(nv))continue;if(nv===0)break;anv=nv;if(anv<0)anv=anv*-1;if(anv>maxv)maxv=anv;clause.push(nv);}
if(clause)clauses.push(clause);}
clauses.unshift(maxv);return clauses;}
exports.parse_formula=function(txt){var tmp,exp,pos;tmp=parse_expression_tree(txt,0);if(err_data(tmp))return tmp;exp=tmp[0];pos=tmp[1];tmp=parse_skip(txt,pos);if(tmp<txt.length)
return(parse_error("remaining text at "+txt.substring(pos)));else
return exp;}
function parse_expression_tree(txt,pos){var isneg,exp,op,node,tmp;pos=parse_skip(txt,pos);isneg=false;if(parse_isatpos(txt,pos,"-")){isneg=true;pos++;}
else if(parse_isatpos(txt,pos,"~")){isneg=true;pos++;}
tmp=parse_term_tree(txt,pos);if(err_data(tmp))return tmp;exp=tmp[0];pos=tmp[1];if(isneg)exp=["-",exp];pos=parse_skip(txt,pos);while(true){op=null;if(parse_isatpos(txt,pos,"&")===true){op="&";pos++;}
else if(parse_isatpos(txt,pos,"and")===true){op="&";pos+=3;}
else if(parse_isatpos(txt,pos,"+")===true){op="+";pos++;}
else if(parse_isatpos(txt,pos,"xor")===true){op="+";pos+=3;}
else if(parse_isatpos(txt,pos,"|")===true){op="V";pos++;}
else if(parse_isatpos(txt,pos,"v")===true){op="V";pos++;}
else if(parse_isatpos(txt,pos,"V")===true){op="V";pos++;}
else if(parse_isatpos(txt,pos,"or")===true){op="V";pos+=3;}
else if(parse_isatpos(txt,pos,"->")===true){op="->";pos+=2;}
else if(parse_isatpos(txt,pos,"=>")===true){op="->";pos+=2;}
else if(parse_isatpos(txt,pos,"<->")===true){op="<->";pos+=3;}
else if(parse_isatpos(txt,pos,"<=>")===true){op="<->";pos+=3;}
if(op===null)break;tmp=parse_term_tree(txt,pos);if(err_data(tmp))return tmp;exp=[op,exp,tmp[0]];pos=tmp[1];pos=parse_skip(txt,pos);if(pos>=txt.length)break;}
return[exp,pos];}
function parse_term_tree(txt,pos){var c,n,j,v,tmp,exp,found,isneg;pos=parse_skip(txt,pos);isneg=false;if(parse_isatpos(txt,pos,"-")){isneg=true;pos++;pos=parse_skip(txt,pos);}
else if(parse_isatpos(txt,pos,"~")){isneg=true;pos++;pos=parse_skip(txt,pos);}
j=pos;found=false;v=null;while(true){c=txt.charAt(j);n=txt.charCodeAt(j);if(j<txt.length&&((n>=48&&n<=57)||(n>=65&&n<=122))){j++;continue;}
if(j>pos){v=txt.substring(pos,j);if(isneg)return[["-",v],j];return[v,j];}
break;}
if(c==="("){pos++;tmp=parse_expression_tree(txt,pos);if(err_data(tmp))return tmp;exp=tmp[0];pos=tmp[1];pos=parse_skip(txt,pos);if(txt.charAt(pos)!==")")
return(parse_error("right parenthesis missing"));pos++;if(isneg)return[["-",exp],pos];return[exp,pos];}else if(c===")"){return(parse_error("extra right parenthesis at "+txt.substring(pos)));}else{return(parse_error("unexpected text "+c+" encountered at "+txt.substring(pos)));}}
function parse_isatpos(txt,pos,str){if(str.length===1){if(txt.charAt(pos)===str)return true;else return false;}else{if(txt.substr(pos,str.length)===str)return true;else return false;}}
function parse_skip(txt,pos){var c;while(pos<txt.length){c=txt.charAt(pos);if(c===" "||c==="\t"||c==="\n"||c==="\r")pos++;else break;}
return pos;}
function parse_error(txt){return["error",txt];}
function err_data(data){if(typeof data!=="string"&&data[0]==="error")return true;else return false;}})(this.proplog_parse={});
(function(exports){"use strict";var maxvarnr=0;var printlen=0;var printlst=[];var printarray=[];exports.parsed_print=function(data,origvars){var tmp;tmp=typeof data;if(!data)return"";if(tmp==="number"||tmp==="string")return String(data);if(data.length<1)return"";if(typeof data[0]==="string")
return formula_print(data,origvars);else
return clauses_print(data,origvars);}
function formula_print(data,origvars){var tmp,res;printlst=[];printlen=0;formula_print_aux(data,origvars,0);res=printlst.join("");res=res.replace(/\"/g,"");return res;}
function formula_print_aux(data,origvars,depth){var tmp,nr,s,op,i;tmp=typeof data;if(!data)return;if(tmp==="number"){nr=data;if(data<0){printlst.push("-");printlen++;nr=0-data;}
tmp=origvars[nr];if(tmp){nr=tmp}
s=String(nr);printlst.push(s);printlen+=s.length;return;}else if(tmp==="string"){printlst.push(data);printlen+=data.length;return;}
if(data.length<2)return;op=data[0];if(op==="-"){printlst.push("-");printlen++;tmp=typeof data[1];formula_print_aux(data[1],origvars,depth+1);}else{if(depth>0){printlst.push("(");printlen+=1;}
for(i=1;i<data.length;i++){formula_print_aux(data[i],origvars,depth+1);if(i<data.length-1){printlst.push(" "+op+" ");printlen+=op.length+2;}}
if(depth>0){printlst.push(")");printlen+=1;}}}
function clauses_print(data,origvars){var i,j,c,lit,s,nr,sign,lit,tmp,res;printlst=[];printlen=0;for(i=0;i<data.length;i++){c=data[i];if(c.length!=1){printlst.push("(");printlen++;}
for(j=0;j<c.length;j++){lit=c[j];sign="";tmp=typeof lit;if(tmp==="string"){s=String(lit);}else if(tmp==="number"){if(lit<0){nr=0-lit;sign="-";}
else{nr=lit;}
if(origvars[nr])s=origvars[nr];else s=String(nr);}else if(lit[0]==="-"){s=lit[1];sign="-";}
printlst.push(sign+s);printlen+=sign.length+s.length;if(j<c.length-1){printlst.push(" V ");printlen+=3;}}
if(j!=1){printlst.push(")");printlen++;}
if(i<data.length-1){printlst.push(" & ");printlen+=3;}
printlst.push("\n");printlen++;}
res=printlst.join("");res=res.replace(/\"/g,"");return res;}
exports.rename_vars_in_clauses=function(clauses){var renamedvars={},origvars=[];var i,j,clause,lit,nr,neg,count=0;for(i=0;i<clauses.length;i++){clause=clauses[i];for(j=0;j<clause.length;j++){lit=clause[j];neg=false;if(typeof lit==="string"){if(lit.lastIndexOf("-",0)===0){nr=lit.substring(1);neg=true}
else nr=lit;}else if(typeof lit==="number"){if(lit<0){nr=0-lit;neg=true}
else nr=lit;}else if(lit.length===2&&lit[0]==="-"){nr=lit[1];neg=true;}else{return[0,"error: not a clause list",[]];}
if(!renamedvars[nr]){count++;renamedvars[nr]=count;origvars[count]=nr;nr=count;}else{nr=renamedvars[nr];}
if(neg)clause[j]=0-nr;else clause[j]=nr;}}
return[count,clauses,origvars];}
exports.rename_vars_in_formula=function(tree){var renamedvars={},origvars=[];var res,tmp;maxvarnr=0;if(typeof tree==="number"||typeof tree==="string"){return[1,1,[0,tree]];}else{rename_vars_in_formula_aux(tree,origvars,renamedvars);return[maxvarnr,tree,origvars];}}
function rename_vars_in_formula_aux(tree,origvars,renamedvars){var i,el,tmp;for(i=1;i<tree.length;i++){el=tree[i];tmp=typeof el;if(tmp==="number"||tmp==="string"){if(!renamedvars[el]){maxvarnr++;renamedvars[el]=maxvarnr;origvars[maxvarnr]=el;tree[i]=maxvarnr;}else{tree[i]=renamedvars[el];}}else{rename_vars_in_formula_aux(el,origvars,renamedvars);}}}
exports.formula_to_cnf=function(frm){var pass1,pass2,tmp,res,i,c;pass1=formula_negpush(frm,true);if(pass1==="error")return pass1;pass2=formula_cnf_distribute(pass1);tmp=typeof pass2;if(tmp==="string"||tmp==="number"||pass2[0]==="-"){return[[pass2]];}else if(pass2[0]==="V"){pass2.shift();return[pass2];}else{res=[];for(i=1;i<pass2.length;i++){c=pass2[i];tmp=typeof c;if(tmp==="string"||tmp==="number"||c[0]==="-"){res.push([c]);}else{c.shift();res.push(c);}}}
return res;}
function formula_negpush(frm,sign){var tmp,op,res,i;tmp=typeof frm;if(tmp==="number"||tmp==="string"){if(sign)return frm;if(tmp==="number")return 0-frm;else if(tmp==="string"&&frm.lastIndexOf("-",0)===0)return frm.substring(1);else return["-",frm];}else{if(frm.length<2)return["error","op must have some arguments"];op=frm[0];if(op==="-"){return formula_negpush(frm[1],!sign);}else if(op==="&"||op==="V"){if(sign)res=[op];else if(op==="&")res=["V"];else res=["&"];for(i=1;i<frm.length;i++){res.push(formula_negpush(frm[i],sign));}
return res;}else if(op==="->"){if(sign)res=["V"];else res=["&"];for(i=1;i<frm.length-1;i++){res.push(formula_negpush(frm[i],!sign));}
res.push(formula_negpush(frm[frm.length-1],sign));return res;}else if(op==="+"){if(frm.length!==3)return["error","+ must have two arguments"]
if(sign){res=["V",["&",formula_negpush(frm[1],false),formula_negpush(frm[2],true)],["&",formula_negpush(frm[1],true),formula_negpush(frm[2],false)]];}else{res=["V",["&",formula_negpush(frm[1],true),formula_negpush(frm[2],true)],["&",formula_negpush(frm[1],false),formula_negpush(frm[2],false)]];}
return res;}else if(op==="<->"){if(frm.length!==3)return["error","<-> must have two arguments"]
if(sign){res=["&",["V",formula_negpush(frm[1],false),formula_negpush(frm[2],true)],["V",formula_negpush(frm[1],true),formula_negpush(frm[2],false)]];}else{res=["V",["&",formula_negpush(frm[1],true),formula_negpush(frm[2],false)],["&",formula_negpush(frm[1],false),formula_negpush(frm[2],true)]];}
return res;}else{return"error";}}}
function formula_cnf_distribute(frm){var op,res,i,j,k,el,tmp,simp,comp;tmp=typeof frm;if(tmp==="number"||tmp==="string"){return frm;}else{op=frm[0];if(op==="-")return frm;if(op==="&"){res=["&"];for(j=1;j<frm.length;j++){el=formula_cnf_distribute(frm[j]);tmp=typeof el;if(tmp==="number"||tmp==="string"||el[0]==="-"||el[0]==="V"){res.push(el);}else{for(k=1;k<el.length;k++){res.push(el[k]);}}}
return res;}else if(op==="V"){simp=["V"];comp=[];for(j=1;j<frm.length;j++){el=formula_cnf_distribute(frm[j]);tmp=typeof el;if(tmp==="number"||tmp==="string"||el[0]==="-"){simp.push(el);}else if(el[0]==="&"){comp.push(el);}else{for(k=1;k<el.length;k++){simp.push(el[k]);}}}
if(comp.length===0)return simp;tmp=combinations(simp,comp);res=["&"];for(j=0;j<tmp.length;j++){res.push(formula_cnf_distribute(tmp[j]));}
return res;}else{return["error","op not allowed"];}}}
function combinations(pre,terms){var i,j,k,term,res,tmp,c;tmp=[pre];res=[];for(i=0;i<terms.length;i++){term=terms[i];res=[];for(j=1;j<term.length;j++){for(k=0;k<tmp.length;k++){c=tmp[k].slice();c.push(term[j]);res.push(c);}}
tmp=res;}
return res;}
exports.print_truthtable=function(data){var tmp,count,frm,syntax,origvars,res;if(!data)return"";if(typeof data[0]==="number"){syntax="dpll";data.shift();tmp=exports.rename_vars_in_clauses(data);}else{syntax="formula";tmp=exports.rename_vars_in_formula(data);}
count=tmp[0];frm=tmp[1];origvars=tmp[2];res=truthtable(frm,syntax,count,origvars);return res;}
function truthtable(frm,syntax,maxvarnr,origvars){var rowcount,v,val,i,j,k,n,r,s,s2,frmstr,row;var varvals;var reslst,res;varvals=new Int32Array(maxvarnr+1);reslst=[];v=[];printlst=[];printlen=0;if(syntax==="dpll"){frmstr="value";for(i=1;i<origvars.length;i++)origvars[i]=String(origvars[i]);}else{frm=add_print_pos_to_formula(frm,origvars,0);frmstr=printlst.join("");frmstr=frmstr.replace(/\"/g,"");printarray=[];for(i=0;i<frmstr.length;i++)printarray.push("&nbsp;");}
for(k=1;k<=maxvarnr;k++)v.push(origvars[k]);s=v.join(" ")+" | "+frmstr;reslst.push(s);s2="";for(k=0;k<s.length;k++)s2+="&ndash;";reslst.push(s2);rowcount=Math.pow(2,maxvarnr);if(rowcount>1024)
return"Table would contain "+rowcount+" rows: our printing limit is 1024 rows.";for(i=0;i<rowcount;i++){v=[];n=i;for(j=1;j<=maxvarnr;j++){n=i>>>(maxvarnr-j);r=n%2;if(!r)varvals[j]=0;else varvals[j]=1;v.push(varvals[j]);s="";for(k=0;k<origvars[j].length;k++)s+="&nbsp;";v.push(s);}
if(syntax=="dpll"){val=print_eval_dpll(frm,varvals);s=val;}else{val=print_eval_formula(frm,varvals,0);s=printarray.join("");}
v.push("&#124; ");v.push(s);reslst.push(v.join(""));}
res=reslst.join("\n");return res;}
function print_eval_dpll(lst,varvals){var i,j,c,found,lit,nr,sign;for(i=0;i<lst.length;i++){c=lst[i];found=false;for(j=0;j<c.length;j++){lit=c[j];if(lit<0){nr=0-lit;sign=0;}
else{nr=lit;sign=1;}
if(varvals[nr]==sign){found=true;break;}}
if(!found)return"0";}
return"1";}
function add_print_pos_to_formula(data,origvars,depth){var tmp,nr,s,op,i,lst,oppos;tmp=typeof data;if(!data)return;if(tmp==="number"){nr=data;if(data<0){printlst.push("-");printlen++;nr=0-data;}
tmp=origvars[nr];if(tmp){nr=tmp}
s=String(nr);printlst.push(s);printlen+=s.length;return data;}else if(tmp==="string"){printlst.push(data);printlen+=data.length;return data;}
if(data.length<2)return null;op=data[0];if(op==="-"){printlst.push("-");oppos=printlen;printlen++;tmp=typeof data[1];return["-",oppos,add_print_pos_to_formula(data[1],origvars,depth+1)];}else{lst=[op,0];if(depth>0){printlst.push("(");printlen+=1;}
for(i=1;i<data.length;i++){lst.push(add_print_pos_to_formula(data[i],origvars,depth+1));if(i<data.length-1){printlst.push(" "+op+" ");oppos=printlen+1;printlen+=op.length+2;}}
if(depth>0){printlst.push(")");printlen+=1;}
lst[1]=oppos;return lst;}}
function print_eval_formula(frm,varvals,depth){var op,oppos,j,tmp,tmp2,res;tmp=typeof frm;if(tmp==="number")return varvals[frm];op=frm[0];oppos=frm[1];if(op==="-"){tmp=print_eval_formula(frm[2],varvals,depth+1);if(tmp===1)res=0;else res=1;printarray[oppos]=valfmt(res,depth);return res;}else if(op==="V"){res=0;for(j=2;j<frm.length;j++){tmp=print_eval_formula(frm[j],varvals,depth+1);if(tmp===1)res=1;}
printarray[oppos]=valfmt(res,depth);return res;}else if(op==="&"){res=1;for(j=2;j<frm.length;j++){tmp=print_eval_formula(frm[j],varvals,depth+1);if(tmp===0)res=0;}
printarray[oppos]=valfmt(res,depth);return res;}else if(op==="->"){res=0;for(j=2;j<frm.length-1;j++){tmp=print_eval_formula(frm[j],varvals);if(tmp===0)res=1;}
tmp=print_eval_formula(frm[frm.length-1],varvals,depth+1);if(tmp===1)res=1;printarray[oppos]=valfmt(res,depth);return res;}else if(op==="<->"){res=1;tmp=print_eval_formula(frm[2],varvals,depth+1);for(j=3;j<frm.length;j++){tmp2=print_eval_formula(frm[j],varvals,depth+1);if(tmp!==tmp2)res=0;}
printarray[oppos]=valfmt(res,depth);return res;}else if(op==="+"){tmp=print_eval_formula(frm[2],varvals,depth+1);tmp2=print_eval_formula(frm[3],varvals,depth+1);tmp=tmp+tmp2;if(tmp===1)res=1;else res=0;printarray[oppos]=valfmt(res,depth);return res;}
return-1;}
function valfmt(s,depth){if(depth>0)return String(s);else return"<b>"+String(s)+"</b>";}})(this.proplog_convert={});
(function(exports){"use strict";exports.generate_problem=function(n,algorithm){var clauses,res,i;if(!n)return"";n=parseInt(n);if(isNaN(n))return"";if(algorithm==="all_combinations"){clauses=prop_combinations_problem(n);}else if(algorithm==="small_unsat"){clauses=prop_small_unsat_problem(n);}else if(algorithm==="random_3-sat"){clauses=prop_random_3_sat_problem(n);}else{clauses=[];}
res="";for(i=0;i<clauses.length;i++){res=res+clauses[i].join(" ")+"\n";}
return res;}
function prop_combinations_problem(n){var tmp,tmp1,tmp2,res,i;if(n<0)return[];if(n==1)return[[1],[-1]];tmp=prop_combinations_problem(n-1);res=[];for(i=0;i<tmp.length;i++){tmp1=tmp[i].slice();tmp1.push(n);res.push(tmp1);tmp2=tmp[i].slice();tmp2.push(0-n);res.push(tmp2);}
return res;}
function prop_small_unsat_problem(n){var res,clause,i;res=[];clause=[];for(i=1;i<=n;i++)clause.push(i);res.push(clause);for(i=1;i<=n;i++)res.push([0-i]);return res;}
function prop_random_3_sat_problem(n){var res,clause,nr,i,j,r1,r2,s,v,ok;if(n<2)return[];nr=n*4;res=[];for(i=0;i<nr;i++){clause=[];for(j=0;j<3;j++){r1=Math.random();if(r1<0.5)s=0-1;else s=1;r2=Math.random();v=Math.floor((r2*n)+1);if(clause.indexOf(s*v)<0){clause.push(s*v);}}
res.push(clause);}
return res;}})(this.proplog_generate={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var conflicts_count=0;var decisions_count=0;var propagations_count=0;var learned_count=0;var restarts_count=0;var reductions_count=0;var max_level_count=0;var units_derived_count=0;var ACTIVITY_DECAY=0.95;var ACTIVITY_LIMIT=1e100;var RESTART_BASE=128;var LEARNED_FACTOR=0.4;var LEARNED_MINIMUM=500;var LEARNED_GROWTH=1.1;var varvals;var varlevel;var varreason;var varactivities;var savedphase;var seen;var posbuckets;var negbuckets;var trail;var trailend;var qhead;var levelstarts;var decisionlevel;var activity_inc;var origclauses;var learnedclauses;var max_learned;var reduce_pending;exports.cdcl=function(clauses,maxvarnr,trace,varnames){var i,tmp,confl,analysis,learned,backlevel,lit;var conflicts_until_restart,conflicts_at_last_restart;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;conflicts_count=0;decisions_count=0;propagations_count=0;learned_count=0;restarts_count=0;reductions_count=0;max_level_count=0;units_derived_count=0;trace_list=[];result_model=[];tmp=maxvar_and_meta(clauses);maxvarnr=tmp[0];clauses=tmp[1];varvals=new Int32Array(maxvarnr+1);varlevel=new Int32Array(maxvarnr+1);varreason=new Array(maxvarnr+1);savedphase=new Int32Array(maxvarnr+1);seen=new Int32Array(maxvarnr+1);varactivities=new Array(maxvarnr+1);trail=new Int32Array(maxvarnr+1);posbuckets=new Array(maxvarnr+1);negbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++){varvals[i]=0;varlevel[i]=0;varreason[i]=0;savedphase[i]=1;seen[i]=0;varactivities[i]=0;posbuckets[i]=[];negbuckets[i]=[];}
activity_inc=1;trailend=0;qhead=0;decisionlevel=0;levelstarts=[0];clauses=simplify_clause_list(clauses);if(clauses===false){if(trace_flag)print_trace(0,"contradiction found during preprocessing");trace_list.push(statistics_str("preprocessing finished"));return[false,trace_list.join("\r\n")];}
initial_activities(clauses);makebuckets(clauses);origclauses=clauses;learnedclauses=[];reduce_pending=false;max_learned=Math.floor(clauses.length*LEARNED_FACTOR);if(max_learned<LEARNED_MINIMUM)max_learned=LEARNED_MINIMUM;for(i=1;i<=maxvarnr;i++){if(varvals[i]!==0){trail[trailend]=i*varvals[i];trailend++;varlevel[i]=0;varreason[i]=0;}}
conflicts_until_restart=RESTART_BASE*luby(restarts_count);conflicts_at_last_restart=0;while(true){confl=propagate();if(confl!==0){conflicts_count++;if(decisionlevel===0){if(trace_flag)print_trace(0,"conflict without any decisions made");trace_list.push(statistics_str("search finished"));return[false,trace_list.join("\r\n")];}
analysis=analyze(confl);learned=analysis[0];backlevel=analysis[1];if(trace_flag){print_trace(decisionlevel,"learned clause: "+lit_list_to_str(learned)+"and backjumping to level "+backlevel);}
backjump(backlevel);install_learned(learned);decay_activities();if(learnedclauses.length>=max_learned){reduce_pending=true;backjump(0);}else if(conflicts_count-conflicts_at_last_restart>=conflicts_until_restart){restarts_count++;conflicts_at_last_restart=conflicts_count;conflicts_until_restart=RESTART_BASE*luby(restarts_count);if(trace_flag){print_trace(0,"restart nr "+restarts_count+", next restart after "+
conflicts_until_restart+" conflicts");}
backjump(0);}}else{if(reduce_pending&&decisionlevel===0){reduce_learned();reduce_pending=false;}
lit=next_decision();if(lit===0){store_model(varvals);trace_list.push(statistics_str("search finished"));return[result_model,trace_list.join("\r\n")];}
decisionlevel++;levelstarts.push(trailend);if(decisionlevel>max_level_count)max_level_count=decisionlevel;if(trace_flag)print_trace(decisionlevel,"deciding "+showvar(lit));enqueue(lit,0);}}}
function propagate(){var dlit,negdlit,bucket,bucketlen,i,j,clause,otherw,lit,nr,polarity,found;while(qhead<trailend){dlit=trail[qhead];qhead++;propagations_count++;negdlit=0-dlit;if(dlit<0)bucket=posbuckets[negdlit];else bucket=negbuckets[dlit];bucketlen=bucket[0];for(i=1;i<=bucketlen;i++){clause=bucket[i];if(clause[0]===negdlit)otherw=clause[1];else otherw=clause[0];if(otherw<0){nr=0-otherw;polarity=-1}
else{nr=otherw;polarity=1};if(varvals[nr]===polarity)continue;found=0;for(j=2;j<clause.length;j++){lit=clause[j];if(lit===otherw)continue;if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};if(varvals[nr]!==(0-polarity)){found=lit;break;}}
if(found!==0){if(clause[0]===negdlit)clause[0]=found;else clause[1]=found;addwatch(found,clause);bucket[i]=bucket[bucketlen];bucket[0]--;bucketlen--;i--;continue;}
if(otherw<0){nr=0-otherw;polarity=-1}
else{nr=otherw;polarity=1};if(varvals[nr]===(0-polarity)){if(trace_flag)print_trace(decisionlevel,"conflict in clause: "+clause_to_str(clause));return clause;}
enqueue(otherw,clause);if(trace_flag){print_trace(decisionlevel,"derived "+showvar(otherw)+" from clause: "+clause_to_str(clause));}}}
return 0;}
function enqueue(lit,reason){var nr;if(lit<0){nr=0-lit;varvals[nr]=-1}
else{nr=lit;varvals[nr]=1};varlevel[nr]=decisionlevel;varreason[nr]=reason;trail[trailend]=lit;trailend++;if(decisionlevel===0)units_derived_count++;}
function addwatch(lit,clause){var bucket;if(lit<0)bucket=negbuckets[0-lit];else bucket=posbuckets[lit];bucket[0]++;if(bucket[0]>=bucket.length)bucket.push(clause);else bucket[bucket[0]]=clause;}
function next_decision(){var i,activity,bestfound,maxactivity;maxactivity=-1;bestfound=0;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)continue;activity=varactivities[i];if(activity>=maxactivity){maxactivity=activity;bestfound=i;}}
if(bestfound===0)return 0;decisions_count++;return bestfound*savedphase[bestfound];}
function analyze(confl){var lits,minimized,counter,lit,litvar,index,c,j,q,v,k,best,backlevel;lits=[0];counter=0;lit=0;litvar=0;index=trailend-1;c=confl;do{for(j=2;j<c.length;j++){q=c[j];if(q<0)v=0-q;else v=q;if(v===litvar)continue;if(seen[v]!==0)continue;if(varlevel[v]===0)continue;seen[v]=1;bump_activity(v);if(varlevel[v]===decisionlevel)counter++;else lits.push(q);}
while(true){lit=trail[index];index--;if(lit<0)litvar=0-lit;else litvar=lit;if(seen[litvar]!==0)break;}
seen[litvar]=0;counter--;c=varreason[litvar];}while(counter>0);lits[0]=0-lit;seen[absvar(lits[0])]=1;minimized=minimize_learned(lits);for(k=0;k<lits.length;k++)seen[absvar(lits[k])]=0;lits=minimized;if(lits.length===1){backlevel=0;}else{best=1;for(k=2;k<lits.length;k++){if(varlevel[absvar(lits[k])]>varlevel[absvar(lits[best])])best=k;}
q=lits[1];lits[1]=lits[best];lits[best]=q;backlevel=varlevel[absvar(lits[1])];}
return[lits,backlevel];}
function minimize_learned(lits){var out,k,j,v,q,reason,redundant;out=[lits[0]];for(k=1;k<lits.length;k++){v=absvar(lits[k]);reason=varreason[v];if(reason===0){out.push(lits[k]);continue;}
redundant=true;for(j=2;j<reason.length;j++){q=absvar(reason[j]);if(q===v)continue;if(seen[q]===0&&varlevel[q]>0){redundant=false;break;}}
if(!redundant)out.push(lits[k]);}
return out;}
function backjump(level){var k,lit,nr,firstundone;if(level>=decisionlevel)return;firstundone=levelstarts[level+1];for(k=trailend-1;k>=firstundone;k--){lit=trail[k];if(lit<0)nr=0-lit;else nr=lit;savedphase[nr]=varvals[nr];varvals[nr]=0;varreason[nr]=0;}
trailend=firstundone;qhead=trailend;levelstarts.length=level+1;decisionlevel=level;}
function install_learned(lits){var i,clause;learned_count++;if(lits.length===1){enqueue(lits[0],0);return;}
clause=new Int32Array(lits.length+2);clause[0]=lits[0];clause[1]=lits[1];for(i=0;i<lits.length;i++)clause[i+2]=lits[i];addwatch(lits[0],clause);addwatch(lits[1],clause);learnedclauses.push(clause);enqueue(lits[0],clause);}
function reduce_learned(){var i,keep;reductions_count++;learnedclauses.sort(function(a,b){return a.length-b.length});keep=Math.floor(learnedclauses.length/2);learnedclauses.length=keep;for(i=1;i<varvals.length;i++){posbuckets[i]=[0];negbuckets[i]=[0];}
for(i=0;i<origclauses.length;i++)watch_clause(origclauses[i]);for(i=0;i<learnedclauses.length;i++)watch_clause(learnedclauses[i]);max_learned=Math.floor(max_learned*LEARNED_GROWTH);if(trace_flag){print_trace(0,"learned clauses cut down to "+keep+", next reduction at "+max_learned);}}
function watch_clause(clause){var j,lit,nr,polarity,first,second;first=0;second=0;for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};if(varvals[nr]===polarity)return;if(varvals[nr]===0){if(first===0)first=lit;else if(second===0)second=lit;}}
if(second===0){first=clause[2];second=clause[3];}
clause[0]=first;clause[1]=second;addwatch(first,clause);addwatch(second,clause);}
function bump_activity(v){var i;varactivities[v]+=activity_inc;if(varactivities[v]>ACTIVITY_LIMIT){for(i=1;i<varactivities.length;i++)varactivities[i]=varactivities[i]/ACTIVITY_LIMIT;activity_inc=activity_inc/ACTIVITY_LIMIT;}}
function decay_activities(){activity_inc=activity_inc/ACTIVITY_DECAY;}
function luby(x){var size,seq;for(size=1,seq=0;size<x+1;seq++,size=2*size+1){}
while(size-1!==x){size=(size-1)>>1;seq--;x=x%size;}
return Math.pow(2,seq);}
function maxvar_and_meta(clauses){var i,j,c,nc,clen,lit,nr,maxvarnr,clauses2;maxvarnr=0;clauses2=[];for(i=0;i<clauses.length;i++){c=clauses[i];clen=c.length;nc=new Int32Array(clen+2);nc[0]=0;nc[1]=0;for(j=0;j<clen;j++){lit=c[j];nc[j+2]=lit;if(lit<0)nr=0-lit;else nr=lit;if(nr>maxvarnr)maxvarnr=nr;}
clauses2.push(nc);}
return[maxvarnr,clauses2];}
function simplify_clause_list(clauses){var clauses2,i,j,k,clause,lit,nlit,nr,sign,remove,cuts,dups,nlen,nc,s;clauses=clauses.sort(function(a,b){return a.length-b.length});clauses2=[];for(i=0;i<clauses.length;i++){clause=clauses[i];remove=false;cuts=0;dups=0;for(j=2;j<clause.length;j++){lit=clause[j];nlit=0-lit;if(lit<0){nr=0-lit;sign=-1;}
else{nr=lit;sign=1;}
if(varvals[nr]===sign){remove=true;break;}
if(varvals[nr]===0-sign){clause[j]=0;cuts++;continue;}
for(k=2;k<j;k++){if(clause[k]===nlit){remove=true;break;}
if(clause[k]===lit){clause[j]=0;dups++;}}
if(remove)break;}
if(remove)continue;nlen=clause.length-(cuts+dups);if(nlen===2)return false;if(nlen===3){units_derived_count++;for(k=2;k<clause.length;k++){if(clause[k]!==0){lit=clause[k];break;}}
if(lit<0){nr=0-lit;sign=-1;}
else{nr=lit;sign=1;}
varvals[nr]=sign;continue;}
if(nlen!==clause.length){nc=new Int32Array(nlen);nc[0]=clause[0];nc[1]=clause[1];k=2;for(j=2;j<clause.length;j++){if(clause[j]===0)continue;nc[k]=clause[j];k++;}
clause=nc;}
clauses2.push(clause);}
if(trace_flag){s="units detected or derived during preprocessing: ";for(i=1;i<varvals.length;i++){if(varvals[i]!==0)s+=" "+showvar(i*varvals[i]);}
print_trace(0,s);}
return clauses2;}
function initial_activities(clauses){var i,j,clause,nlits,lit,nr,bonus;for(i=0;i<clauses.length;i++){clause=clauses[i];nlits=clause.length-2;if(nlits<3)bonus=20;else if(nlits<4)bonus=15;else{bonus=10-nlits;if(bonus<1)bonus=1;}
for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0)nr=0-lit;else nr=lit;varactivities[nr]+=bonus;}}
if(trace_flag){var s="initial variable activities: ";for(i=1;i<varactivities.length;i++)s+=showvar(i)+":"+varactivities[i]+" ";print_trace(0,s);}}
function makebuckets(clauses){var i,j,k,clause,lit,bucket;for(i=0;i<clauses.length;i++){clause=clauses[i];k=0;for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0)bucket=negbuckets[0-lit];else bucket=posbuckets[lit];if(k<2){clause[k]=lit;k++;bucket.unshift(clause);}else{bucket.push(0);}}}
for(i=1;i<negbuckets.length;i++){bucket=negbuckets[i];for(j=0;j<bucket.length;j++){if(bucket[j]===0)break;}
negbuckets[i].unshift(j);bucket=posbuckets[i];for(j=0;j<bucket.length;j++){if(bucket[j]===0)break;}
posbuckets[i].unshift(j);}
return clauses;}
function store_model(varvals){var i;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}}
function statistics_str(prefix){var txt;txt=prefix+": conflicts "+conflicts_count;txt+=", decisions "+decisions_count;txt+=", propagations "+propagations_count;txt+=", learned clauses "+learned_count;txt+=", restarts "+restarts_count;txt+=", learned clause reductions "+reductions_count;txt+=", max level "+max_level_count;txt+=", level 0 units "+units_derived_count;return txt;}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function absvar(lit){if(lit<0)return 0-lit;else return lit;}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}
function clause_to_str(cl){var i,s="";if(cl===true)return"tautology";if(!cl)return"empty";for(i=2;i<cl.length;i++){s+=showvar(cl[i])+" ";}
return s;}
function lit_list_to_str(lst){var i,s="";for(i=0;i<lst.length;i++){s+=showvar(lst[i])+" ";}
return s;}})(this.proplog_cdcl={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var purevars=[];var result_model=[];var unit_propagations_count=0;var var_selections_count=0;var units_derived_count=0;var pure_derived_count=0;var clauses_removed_count=0;var max_depth_count=0;var varactivities;exports.dpll=function(clauses,maxvarnr,trace,varnames){var varvals,occvars,posbuckets,negbuckets,derived,tmp;var i,j,res,txt,v;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;unit_propagations_count=0;var_selections_count=0;units_derived_count=0;pure_derived_count=0;clauses_removed_count=0;max_depth_count=0;trace_list=[];result_model=[];tmp=maxvar_and_meta(clauses);maxvarnr=tmp[0];clauses=tmp[1];derived=new Int32Array(maxvarnr+1);varvals=new Int32Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)varvals[i]=0;occvars=new Int32Array(maxvarnr+1);posbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)posbuckets[i]=[];negbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)negbuckets[i]=[];varactivities=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)varactivities[i]=1;for(i=0;i<clauses.length;i++){if(clauses[i].length===2){if(trace_flag)trace_list.push("an empty clause found in the input");return[false,trace_list.join("\r\n")];}}
clauses=count_occurrences(clauses,varvals,occvars,posbuckets,negbuckets,derived);if(clauses.length===0){store_model(varvals);if(trace_flag)trace_list.push("assignment found during pure literal elimination");result_model=clean_result(result_model,purevars);return[result_model,trace_list.join("\r\n")];}
makebuckets(clauses,varvals,occvars,posbuckets,negbuckets,derived);res=satisfiable_at(0,0,clauses,varvals,occvars,posbuckets,negbuckets,derived);txt="search finished: unit propagations count is "+unit_propagations_count;txt+=", units derived count is "+units_derived_count;txt+=", max depth is "+max_depth_count;trace_list.push(txt);result_model=clean_result(result_model,purevars);if(res)return[result_model,trace_list.join("\r\n")];else return[false,trace_list.join("\r\n")];}
function clean_result(model,purevars){return model;}
function satisfiable_at(derivedlen,depth,clauses,varvals,occvars,posbuckets,negbuckets,derived){var queue,propres,nextvar,sign,errtxt,lit,i,satval,s;if(depth>max_depth_count)max_depth_count=depth;if(derivedlen!==0){if(trace_flag){s="assigning var ";for(i=0;i<derivedlen;i++)s+=showvar(derived[i])+" ";print_trace(depth,s);}
propres=unit_propagate(derivedlen,depth,clauses,varvals,posbuckets,negbuckets,derived);}else{if(trace_flag)print_trace(depth,"search called without assigning vars");propres=0;}
if(propres===true){store_model(varvals);return true;}
if(propres===false)return false;nextvar=next_var(clauses,varvals,occvars);if(nextvar===0){store_model(varvals);return true;}
if(trace_flag)print_trace(depth,"splitting variable "+showvar(nextvar));derived[0]=nextvar;satval=satisfiable_at(1,depth+1,clauses,varvals,occvars,posbuckets,negbuckets,derived);if(satval)return true;derived[0]=0-nextvar;satval=satisfiable_at(1,depth+1,clauses,varvals,occvars,posbuckets,negbuckets,derived);if(satval)return true;if(typeof(propres)==="number"){if(propres<0)varvals[0-propres]=0;else if(propres!==0)varvals[propres]=0;}else{for(i=0;i<propres.length;i++){lit=propres[i];if(lit<0)varvals[0-lit]=0;else varvals[lit]=0;}}
return false;}
function unit_propagate(derivedlen,depth,clauses,varvals,posbuckets,negbuckets,derived){var i,j,dlit,negdlit,lit,nr,vval,polarity,derivednext,allclausesfound;var bucket,bucketlen,tmpbucket,clause,useclause,unassigned_count,unassigned_lit;var assigned,derived_units_txt,activity;unit_propagations_count++;derived_units_txt="";derivednext=0;for(i=0;i<derivedlen;i++){lit=derived[i];if(lit<0)varvals[0-lit]=-1
else varvals[lit]=1;}
while(derivednext<derivedlen){dlit=derived[derivednext++];negdlit=0-dlit;if(dlit<0)bucket=posbuckets[negdlit];else bucket=negbuckets[dlit];bucketlen=bucket[0];for(i=1;i<=bucketlen;i++){clause=bucket[i];useclause=true;unassigned_count=0;unassigned_lit=0;for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0){vval=varvals[0-lit];polarity=-1}
else{vval=varvals[lit];polarity=1};if(vval===0){if(unassigned_count>0){if(clause[0]===negdlit){if(lit===clause[1])lit=unassigned_lit;clause[0]=lit;}else{if(lit===clause[0])lit=unassigned_lit;clause[1]=lit;}
if(lit<0)tmpbucket=negbuckets[0-lit];else tmpbucket=posbuckets[lit];tmpbucket[0]++;tmpbucket[tmpbucket[0]]=clause;bucket[i]=bucket[bucketlen];bucket[0]--;bucketlen--;i--;useclause=false;break;}
unassigned_count++;unassigned_lit=lit;}else if(vval===polarity){useclause=false;break;}}
if(useclause){if(unassigned_count===0){if(trace_flag)print_trace(depth,"value is false");for(j=0;j<derivedlen;j++){lit=derived[j];if(lit<0)varvals[0-lit]=0;else varvals[lit]=0;}
activity=2*(Math.pow(unit_propagations_count,1.5));for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0)varactivities[0-lit]+=activity;else varactivities[lit]+=activity;}
return false;}
units_derived_count++;derived[derivedlen]=unassigned_lit;derivedlen++;if(unassigned_lit<0){nr=0-unassigned_lit;polarity=-1}
else{nr=unassigned_lit;polarity=1};varvals[nr]=polarity;if(trace_flag)derived_units_txt+=unassigned_lit+" ";}}}
if(trace_flag){print_trace(depth,"value is undetermined");if(derived_units_txt.length>0)print_trace(depth,"derived units "+derived_units_txt);}
if(derivedlen===1)return derived[0];assigned=new Int32Array(derivedlen);for(i=0;i<derivedlen;i++)assigned[i]=derived[i];return assigned;}
function next_var(clauses,varvals,occvars){var i,activity,bestfound,maxactivity;var l_varactivities=varactivities;var_selections_count++;maxactivity=-1000;bestfound=0;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)continue;activity=l_varactivities[i];if(activity>=maxactivity){maxactivity=activity;bestfound=i;}}
return bestfound;}
function store_model(varvals){var i;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}}
function maxvar_and_meta(clauses){var i,j,c,nc,clen,lit,nr,maxvarnr,clauses2;maxvarnr=0;clauses2=[];for(i=0;i<clauses.length;i++){c=clauses[i];clen=c.length;nc=new Int32Array(clen+2);nc[0]=0;nc[1]=0;for(j=0;j<clen;j++){lit=c[j];nc[j+2]=lit;if(lit<0)nr=0-lit;else nr=lit;if(nr>maxvarnr)maxvarnr=nr;}
clauses2.push(nc);}
return[maxvarnr,clauses2];}
function count_occurrences(clauses,varvals,occvars,posbuckets,negbuckets,derived){var clauses2,i,j,k,clause,lit,nr,sign,remove;var clen,vval,oval,bonus,s,maxact,tmp;for(i=0;i<clauses.length;i++){clause=clauses[i];clen=clause.length;for(j=2;j<clen;j++){lit=clause[j];if(lit<0){nr=0-lit;sign=-1}
else{nr=lit;sign=1};vval=varvals[nr];if(vval===0){oval=occvars[nr];if(oval===0)occvars[nr]=sign;else if(oval===(0-sign))occvars[nr]=2;else if(oval>=2){if(clen<5)bonus=20;else if(clen<6)bonus=15;else{bonus=10-(clen-2);if(bonus<0)bonus=1;}
occvars[nr]=occvars[nr]+bonus;}}}}
purevars=[];maxact=1;for(i=1;i<occvars.length;i++){oval=occvars[i];if(oval<2){purevars.push(i);varactivities[i]=0;}else{if(varvals[i]!==0){varactivities[i]=0;}else{varactivities[i]=occvars[i];if(varactivities[i]>maxact)maxact=varactivities[i];}}}
if(trace_flag){s="initial variable activities: ";for(i=1;i<varactivities.length;i++){s+=showvar(i)+":"+varactivities[i]+" ";}
print_trace(0,s);}
return clauses;}
function makebuckets(clauses,varvals,occvars,posbuckets,negbuckets,derived){var i,j,k,clause,lit,bucket;for(i=0;i<clauses.length;i++){clause=clauses[i];k=0;for(j=2;j<clause.length;j++){lit=clause[j];if(lit<0)bucket=negbuckets[0-lit];else bucket=posbuckets[lit];if(k<2){clause[k]=lit;k++;bucket.unshift(clause);}else{bucket.push(0);}}}
for(i=1;i<negbuckets.length;i++){bucket=negbuckets[i];for(j=0;j<bucket.length;j++){if(bucket[j]===0)break;}
negbuckets[i].unshift(j);bucket=posbuckets[i];for(j=0;j<bucket.length;j++){if(bucket[j]===0)break;}
posbuckets[i].unshift(j);}
return clauses;}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}
function clause_to_str(cl){var i,s="";if(cl===true)return"tautology";if(!cl)return"empty";for(i=2;i<cl.length;i++){s+=showvar(cl[i])+" ";}
return s;}
function array_to_str(cl){var i,s="";if(cl===true)return"true";if(!cl)return"[]";for(i=0;i<cl.length;i++){s+=cl[i]+" ";}
return s;}
function array_list_to_str(arr){var i,s="";for(i=0;i<arr.length;i++){s+=array_to_str(arr[i])+"; \n";}
return s;}
function clause_list_to_str(lst){var i,s="[";for(i=0;i<lst.length;i++){s+="["+clause_to_str(lst[i])+"]";}
return s+"]";}
function clause_list_list_to_str(lst){var i,s="[";for(i=0;i<lst.length;i++){s+=clause_list_to_str(lst[i]);}
return s+"]";}})(this.proplog_dpll={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var unit_propagations_count=0;var var_selections_count=0;var units_derived_count=0;var pure_derived_count=0;var max_depth_count=0;exports.olddpll=function(clauses,maxvarnr,trace,varnames){var i,j,k,found,res,varvals,occvars,posbuckets,negbuckets,derived;var c,lit,nlit,nr,sign,nextvar,clauses2,tmp,txt;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;unit_propagations_count=0;var_selections_count=0;units_derived_count=0;pure_derived_count=0;max_depth_count=0;trace_list=[];result_model=[];if(!maxvarnr){maxvarnr=0;for(i=0;i<clauses.length;i++){c=clauses[i];for(j=0;j<c.length;j++){if(c[j]<0)nr=0-c[j];else nr=c[j];if(nr>maxvarnr)maxvarnr=nr;}}}
derived=new Int32Array(maxvarnr+1);varvals=new Int32Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)varvals[i]=0;occvars=new Int32Array(maxvarnr+1);posbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)posbuckets[i]=[];negbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)negbuckets[i]=[];clauses=preprocess(clauses,varvals,occvars,posbuckets,negbuckets,derived);res=satisfiable_at(clauses,varvals,0,0,0,occvars,posbuckets,negbuckets,derived);txt="finished: unit propagations count is "+unit_propagations_count;txt+=", units derived count is "+units_derived_count;txt+=", var selections count is "+var_selections_count;txt+=", pure literal count is "+pure_derived_count;txt+=", max depth is "+max_depth_count;trace_list.push(txt);if(res)return[result_model,trace_list.join("\r\n")];else return[false,trace_list.join("\r\n")];}
function preprocess(clauses,varvals,occvars,posbuckets,negbuckets,derived){var propres,nextvar,sign,errtxt,depth;var clauses2,i,j,k,c,lit,nlit,found;clauses2=[];for(i=0;i<clauses.length;i++){c=clauses[i];for(j=0;j<c.length;j++){lit=c[j];nlit=0-lit;found=false;for(k=0;k<j;k++){if(c[k]===nlit){found=true;break;}}
if(found)continue;if(lit<0)negbuckets[nlit].push(c);else posbuckets[lit].push(c);clauses2.push(c);}}
return clauses2;}
function satisfiable_at(clauses,varvals,varnr,val,depth,occvars,posbuckets,negbuckets,derived){var queue,propres,nextvars,nextvar,sign,errtxt,lit,i,satval;if(depth>max_depth_count)max_depth_count=depth;if(varnr!==0){if(trace_flag)print_trace(depth,"assigning var "+showvar(varnr)+" to "+val);derived[0]=varnr*val;propres=unit_propagate(clauses,varvals,1,depth,posbuckets,negbuckets,derived);}else{if(trace_flag)print_trace(depth,"search called without assigning a var before");propres=0;}
if(propres===true){store_model(varvals);return true;}
if(propres===false)return false;nextvars=next_vars(clauses,varvals,occvars);if(nextvars===0){store_model(varvals);return true;}
if((typeof nextvars)!=="number"){pure_derived_count++;nextvar=nextvars[0];if(nextvar<0){nextvar=0-nextvar;sign=0-1;}
else{sign=1;}
if(trace_flag)print_trace(depth,"pure variable "+showvar(nextvar)+", sign "+sign);if(satisfiable_at(clauses,varvals,nextvar,sign,depth+1,occvars,posbuckets,negbuckets,derived)){return true;}else{if(typeof(propres)==="number"){if(propres<0)varvals[0-propres]=0;else if(propres!==0)varvals[propres]=0;}else{for(i=0;i<propres.length;i++){lit=propres[i];if(lit<0)varvals[0-lit]=0;else varvals[lit]=0;}}
return false;}}
nextvar=nextvars;if(trace_flag)print_trace(depth,"splitting variable "+showvar(nextvar));if(trace_flag)print_trace(depth,"splitting variable "+showvar(nextvar));satval=satisfiable_at(clauses,varvals,nextvar,1,depth+1,occvars,posbuckets,negbuckets,derived);if(satval)return true;satval=satisfiable_at(clauses,varvals,nextvar,-1,depth+1,occvars,posbuckets,negbuckets,derived);if(satval)return true;if(typeof(propres)==="number"){if(propres<0)varvals[0-propres]=0;else if(propres!==0)varvals[propres]=0;}else{for(i=0;i<propres.length;i++){lit=propres[i];if(lit<0)varvals[0-lit]=0;else varvals[lit]=0;}}
return false;}
function unit_propagate(clauses,varvals,derivedlen,depth,posbuckets,negbuckets,derived){var i,j,lit,nr,vval,polarity,derivednext,allclausesfound;var bucket,clause,useclause,unassigned_count,unassigned_lit;var assigned,derived_units_txt;unit_propagations_count++;derived_units_txt="";derivednext=0;for(i=0;i<derivedlen;i++){lit=derived[i];if(lit<0)varvals[0-lit]=-1
else varvals[lit]=1;}
while(derivednext<derivedlen){lit=derived[derivednext++];if(lit<0)bucket=posbuckets[0-lit];else bucket=negbuckets[lit];for(i=0;i<bucket.length;i++){clause=bucket[i];useclause=true;unassigned_count=0;unassigned_lit=0;for(j=0;j<clause.length;j++){lit=clause[j];if(lit<0){vval=varvals[0-lit];polarity=-1}
else{vval=varvals[lit];polarity=1};if(vval===0){if(unassigned_count>0){useclause=false;break;}
unassigned_count++;unassigned_lit=lit;}else if(vval===polarity){useclause=false;break;}}
if(useclause){if(unassigned_count===0){if(trace_flag)print_trace(depth,"value is false");for(j=0;j<derivedlen;j++){lit=derived[j];if(lit<0)varvals[0-lit]=0;else varvals[lit]=0;}
return false;}
units_derived_count++;derived[derivedlen]=unassigned_lit;derivedlen++;if(unassigned_lit<0){nr=0-unassigned_lit;polarity=-1}
else{nr=unassigned_lit;polarity=1};varvals[nr]=polarity;if(trace_flag)derived_units_txt+=unassigned_lit+" ";}}}
if(trace_flag){print_trace(depth,"value is undetermined");if(derived_units_txt.length>0)print_trace(depth,"derived units "+derived_units_txt);}
if(derivedlen===1)return derived[0];assigned=new Int32Array(derivedlen);for(i=0;i<derivedlen;i++)assigned[i]=derived[i];return assigned;}
function next_vars(clauses,varvals,occvars){var i,j,lit,nr,vval,oval,polarity,bonus;var clause,clauseval,clen,blen,queue;var_selections_count++;for(i=0;i<occvars.length;i++)occvars[i]=0;for(i=0;i<clauses.length;i++){clause=clauses[i];clauseval=0;clen=clause.length;blen=clen;for(j=0;j<clen;j++){lit=clause[j];if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};vval=varvals[nr];if(vval===polarity){clauseval=1;break;}else if(vval===0-polarity){blen--;}}
if(clauseval===0&&blen>0){for(j=0;j<clen;j++){lit=clause[j];if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};vval=varvals[nr];if(vval===0){oval=occvars[nr];if(oval===0)occvars[nr]=polarity;else if(oval===0-polarity)occvars[nr]=2;else if(oval>=2){if(blen<3)bonus=20;else if(blen<4)bonus=15;else{bonus=10-blen;if(bonus<0)bonus=1;}
occvars[nr]=occvars[nr]+bonus;}}}}}
bonus=0;nr=0;queue=[];for(i=1;i<occvars.length;i++){oval=occvars[i];if(oval===0)continue;if(oval<2&&varvals[i]===0)queue.push(oval*i);if(oval>bonus&&varvals[i]===0){bonus=oval;nr=i;}}
if(queue.length!==0)return queue;if(nr<0)return 0-nr;else if(nr>0)return nr;else{for(i=1;i<varvals.length;i++)if(varvals[i]===0)return i;}
return 0;}
function store_model(varvals){var i;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}
function clause_to_str(cl){var i,s="";if(cl===true)return"tautology";if(!cl)return"empty";for(i=0;i<cl.length;i++){s+=showvar(cl[i])+" ";}
return s;}
function clause_list_to_str(lst){var i,s="[";for(i=0;i<lst.length;i++){s+="["+clause_to_str(lst[i])+"]";}
return s+"]";}
function clause_list_list_to_str(lst){var i,s="[";for(i=0;i<lst.length;i++){s+=clause_list_to_str(lst[i]);}
return s+"]";}})(this.proplog_olddpll={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var unit_propagations_count=0;var units_derived_count=0;var max_depth_count=0;exports.naivedpll=function(clauses,maxvarnr,trace,varnames){var i,j,c,nr,res,varvals,txt;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;unit_propagations_count=0;units_derived_count=0;max_depth_count=0;trace_list=[];result_model=[];if(!maxvarnr){maxvarnr=0;for(i=0;i<clauses.length;i++){c=clauses[i];for(j=0;j<c.length;j++){if(c[j]<0)nr=0-c[j];else nr=c[j];if(nr>maxvarnr)maxvarnr=nr;}}}
varvals=new Int32Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)varvals[i]=0;res=satisfiable_at(clauses,varvals,0,0,0);txt="finished: unit propagations count is "+unit_propagations_count;txt+=", units derived count is "+units_derived_count;txt+=", max depth is "+max_depth_count;trace_list.push(txt);if(res)return[result_model,trace_list.join("\r\n")];else return[false,trace_list.join("\r\n")];}
function satisfiable_at(clauses,varvals,varnr,val,depth){var propres,i,nextvar,sign,errtxt;if(depth>max_depth_count)max_depth_count=depth;if(varnr!==0){if(trace_flag)print_trace(depth,"setting var "+showvar(varnr)+" to "+val);varvals[varnr]=val;}else{if(trace_flag)print_trace(depth,"search called without setting a var before");}
propres=unit_propagate(clauses,varvals,depth);if(propres===1){store_model(varvals);varvals[varnr]=0;return true;}
if(propres===-1){varvals[varnr]=0;return false;}
nextvar=0;for(i=1;i<varvals.length;i++){if(varvals[i]===0){nextvar=i;break;}}
if(nextvar!==0){if(trace_flag)print_trace(depth,"splitting variable "+showvar(nextvar));if(satisfiable_at(clauses,varvals,nextvar,1,depth+1)||satisfiable_at(clauses,varvals,nextvar,-1,depth+1)){return true;}
varvals[nextvar]=0;for(i=0;i<propres.length;i++)varvals[propres[i]]=0;return false;}else{errtxt="Error in the satisfiable_at";console.log(errtxt);show_process(errtxt);}}
function unit_propagate(clauses,varvals,depth){var i,j,lit,nr,vval,polarity;var clause,clauseval,unassigned_count,unassigned_lit,allvarsfound,allclausesfound;var derived_vars,derived_queue,derived_units_txt;unit_propagations_count++;derived_vars=[];derived_units_txt="";while(true){allclausesfound=true;derived_queue=[];for(i=0;i<clauses.length;i++){clause=clauses[i];clauseval=0;unassigned_count=0;unassigned_lit=0;for(j=0;j<clause.length;j++){lit=clause[j];if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};vval=varvals[nr];if(vval===polarity){clauseval=1;break;}else if(vval===0){unassigned_count++;unassigned_lit=lit;}}
if(clauseval===1)continue;if(unassigned_count===0){if(trace_flag)print_trace(depth,"value is false");for(j=0;j<derived_vars.length;j++)varvals[derived_vars[j]]=0;return-1;}else if(unassigned_count===1){units_derived_count++;derived_queue.push(unassigned_lit);}
if(unassigned_count!==0)allclausesfound=false;}
if(allclausesfound){if(trace_flag)print_trace(depth,"value is true");return 1;}
if(derived_queue.length===0){break;}else{for(j=0;j<derived_queue.length;j++){lit=derived_queue[j];if(lit<0){nr=0-lit;polarity=-1}
else{nr=lit;polarity=1};varvals[nr]=polarity;derived_vars.push(nr);if(trace_flag)derived_units_txt+=showvar(lit)+" ";}}}
if(trace_flag){print_trace(depth,"value is undetermined");if(derived_vars.length>0)print_trace(depth,"derived units "+derived_units_txt);}
return derived_vars;}
function store_model(varvals){var i;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}})(this.proplog_naivedpll={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var truth_value_leaves_count=0;var truth_value_calc_count=0;var truth_check_place="nodes";exports.searchtable=function(clauses,maxvarnr,algorithm,trace,varnames){var i,j,c,nr,varvals,res,txt;truth_check_place=algorithm;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;truth_value_calc_count=0;truth_value_leaves_count=0;trace_list=[];result_model=[];if(!maxvarnr){maxvarnr=0;for(i=0;i<clauses.length;i++){c=clauses[i];for(j=0;j<c.length;j++){if(c[j]<0)nr=0-c[j];else nr=c[j];if(nr>maxvarnr)maxvarnr=nr;}}}
varvals=new Int32Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)varvals[i]=0;res=satisfiable_by_table_at(clauses,varvals,1,1,1)||satisfiable_by_table_at(clauses,varvals,1,-1,1);txt="finished: evaluations count is "+truth_value_calc_count;txt+=", leaves count is "+truth_value_leaves_count;trace_list.push(txt);if(res)return[result_model,trace_list.join("\r\n")];else return[false,trace_list.join("\r\n")];}
function satisfiable_by_table_at(clauses,varvals,varnr,val,depth){var tmp,errtxt;varvals[varnr]=val;if(varnr===varvals.length-1)truth_value_leaves_count++;if(trace_flag)print_trace(depth,"setting var "+showvar(varnr)+" to "+val);if(truth_check_place!=="leaves"||varnr===varvals.length-1){tmp=clauses_truth_value_at(clauses,varvals,depth);if(tmp===1){store_model(varvals);varvals[varnr]=0;return true;}
if(tmp===-1){varvals[varnr]=0;return false;}}
if(varnr<varvals.length-1){if(satisfiable_by_table_at(clauses,varvals,varnr+1,1,depth+1)||satisfiable_by_table_at(clauses,varvals,varnr+1,-1,depth+1)){varvals[varnr]=0;return true;}
varvals[varnr]=0;return false;}else{errtxt="Error in the satisfiable_by_table algorithm";console.log(errtxt);show_process(errtxt);}}
function store_model(varvals){var i;for(i=1;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}}
function clauses_truth_value_at(clauses,varvals,depth){var i,j,nr,vval,polarity;var clause,clauseval,allvarsfound,allclausesfound;truth_value_calc_count++;allclausesfound=true;for(i=0;i<clauses.length;i++){clause=clauses[i];clauseval=0;allvarsfound=true;for(j=0;j<clause.length;j++){nr=clause[j];polarity=1;if(nr<0){nr=nr*-1;polarity=-1};vval=varvals[nr];if(vval===polarity){clauseval=1;break;}else if(vval===0){allvarsfound=false;}}
if(clauseval!==1&&allvarsfound){if(trace_flag)print_trace(depth,"value is false");return-1;}
if(!allvarsfound)allclausesfound=false;}
if(allclausesfound){if(trace_flag)print_trace(depth,"value is true");return 1;}
if(trace_flag)print_trace(depth,"value is undetermined");return 0;}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}})(this.proplog_searchtable={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var selected_clauses_count=0;var generated_clauses_count=0;var kept_clauses_count=0;exports.naiveres=function(clauses,maxvarnr,trace,varnames){var usable_clauses,processed_clauses,selected,processed;var tmp_array;var p,found,i,j,sl,nsl,derived,result,txt;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;selected_clauses_count=0;generated_clauses_count=0;kept_clauses_count=0;trace_list=[];result_model=[];processed_clauses=[];usable_clauses=clauses;tmp_array=new Int32Array(maxvarnr*2+1);result=true;while(usable_clauses.length>0){selected=usable_clauses.shift();if(trace_flag)print_trace(0,"selected "+clause_to_str(selected));found=false;for(p=0;p<processed_clauses.length;p++){if(naive_subsumed(processed_clauses[p],selected)){found=true;break;}}
if(found){if(trace_flag)print_trace(1," was subsumed");continue;}
selected_clauses_count++;for(p=0;p<processed_clauses.length;p++){processed=processed_clauses[p];if(trace_flag)print_trace(2,"processed "+clause_to_str(processed));for(i=0;i<selected.length;i++){sl=selected[i];nsl=0-sl;for(j=0;j<processed.length;j++){if(nsl===processed[j]){generated_clauses_count++;derived=naive_merge_rest(selected,processed,i,j,tmp_array);if(trace_flag)print_trace(4,"derived "+clause_to_str(derived));if(derived===false){result=false;break;}
if(derived===true)continue;kept_clauses_count++;usable_clauses.push(derived);}}}
if(!result)break;}
if(!result)break;processed_clauses.push(selected);}
txt="finished: selected clauses: "+selected_clauses_count;txt+=", generated clauses: "+generated_clauses_count;txt+=", kept clauses: "+kept_clauses_count;trace_list.push(txt);if(result){result_model=true;return[result_model,trace_list.join("\r\n")];}
else{return[false,trace_list.join("\r\n")];}}
function naive_merge_rest(c1,c2,i1,i2,tmp_array){var varcount,num,c,pos,i,j,l,nl,res,found;varcount=0;for(num=1;num<3;num++){if(num===1){c=c1;pos=i1;}
else{c=c2;pos=i2;}
for(i=0;i<c.length;i++){if(i===pos)continue;l=c[i];nl=(0-l);found=false;for(j=0;j<varcount;j++){if(tmp_array[j]===l){found=true;break;}
if(tmp_array[j]===nl){return true;}}
if(!found)tmp_array[varcount++]=l;}}
if(varcount===0)return false;res=new Int32Array(varcount);for(j=0;j<varcount;j++)res[j]=tmp_array[j];return res;}
function naive_subsumed(c1,c2){var i,j,lit,found;if(c1.length>c2.length)return false;j=0;for(i=0;i<c1.length;i++){lit=c1[i];found=false;for(j=0;j<c2.length;j++){if(c2[j]===lit){found=true;break;}}
if(!found)return false;}
return true;}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}
function clause_to_str(cl){var i,s="";if(cl===true)return"tautology";if(!cl)return"empty";for(i=0;i<cl.length;i++){s+=showvar(cl[i])+" ";}
return s;}})(this.proplog_naiveres={});
(function(exports){"use strict";var trace_flag=false;var trace_method="text";var trace_list=[];var origvars=[];var result_model=[];var selected_clauses_count=0;var generated_clauses_count=0;var kept_clauses_count=0;exports.resolution=function(clauses,maxvarnr,trace,varnames){var varvals,usable_clauses,processed_clauses,selected,processed;var posbuckets,negbuckets,bucket,poscount,txt;var tmp_array,var_vals;var i,j,c,lit,s,vn,p,sl,nsl,nr,sign,derived,kept,l,horn_flag,result;if(trace){trace_flag=true;trace_method=trace;}
else{trace_flag=false;}
if(varnames)origvars=varnames;else origvars=false;selected_clauses_count=0;generated_clauses_count=0;kept_clauses_count=0;trace_list=[];result_model=[];processed_clauses=[];tmp_array=new Int32Array(maxvarnr*2+1);varvals=new Int32Array(maxvarnr+1);for(i=0;i<maxvarnr+1;i++)varvals[i]=0;usable_clauses=new Array(100);for(i=0;i<100;i++)usable_clauses[i]=[];if(trace_flag)print_trace(0,"starting to process input unit clauses");for(i=0;i<clauses.length;i++){c=clauses[i];if(c.length!==1)continue;lit=c[0];if(lit<0){s=-1;vn=0-lit;}
else{s=1;vn=lit;}
if(varvals[vn]!==0){if(varvals[vn]===s)continue;print_trace(0,"empty clause derived from "+clause_to_str(c));trace_list.push("Finished while preprocessing.");return[false,trace_list.join("\r\n")];}
store_to_varvals(c[0],varvals);store_to_usable(c,usable_clauses);}
if(trace_flag)print_trace(0,"input unit clauses processed, starting to process non-unit");horn_flag=true;for(i=0;i<clauses.length;i++){c=clauses[i];if(c.length<2)continue;if(tautology(c))continue;c=quick_sort_in_place(c);c=pre_preprocess_clause(c,varvals,[],tmp_array);if(c===false){if(trace_flag)print_trace(0,"empty clause derived from "+clause_to_str(clauses[i]));trace_list.push("Finished while preprocessing.");return[false,trace_list.join("\r\n")];}
if(c===true)continue;store_to_usable(c,usable_clauses);if(horn_flag){poscount=0;for(j=0;j<c.length;j++){if(c[j]<0)continue;poscount++;if(poscount>1){horn_flag=false;break;}}}}
if(trace_flag){print_trace(0,"input non-unit clauses processed ");if(horn_flag)print_trace(0,"observation: clause set is horn");else print_trace(0,"observation: clause set is not horn");}
posbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)posbuckets[i]=[];negbuckets=new Array(maxvarnr+1);for(i=0;i<=maxvarnr;i++)negbuckets[i]=[];result=true;while(selected=pick_selected(usable_clauses)){if(trace_flag)print_trace(0,"selected candidate "+clause_to_str(selected));selected=preprocess_clause(selected,varvals,processed_clauses,posbuckets,negbuckets,tmp_array);if(!selected){result=false;break;}
if(selected===true){if(trace_flag)print_trace(1,"subsumed");continue;}
if(trace_flag)print_trace(0,"preprocessed to "+clause_to_str(selected));selected_clauses_count++;sl=selected[0];if(sl<0){nr=0-sl;sign=-1;bucket=posbuckets[nr];}
else{nr=sl;sign=1;bucket=negbuckets[nr];}
nsl=0-sl;for(p=0;p<bucket.length;p++){processed=bucket[p];if(processed===true)continue;if(trace_flag)print_trace(2,"processed "+clause_to_str(processed));generated_clauses_count++;derived=merge_rest(selected,processed,0,0,tmp_array,varvals);if(derived===false){result=false;break;}
if(derived===true){if(trace_flag)print_trace(4,"derived clause a tautology or subsumed");continue;}
kept_clauses_count++;if(derived.length===1)store_to_varvals(derived[0],varvals);if(trace_flag)print_trace(4,"kept "+clause_to_str(derived));store_to_usable(derived,usable_clauses);if(ordered_subsumed(derived,processed))bucket[p]=true;}
if(!result)break;if(selected.length===1)store_to_varvals(selected[0],varvals);store_to_processed(selected,processed_clauses,posbuckets,negbuckets);}
txt="finished: selected clauses: "+selected_clauses_count;txt+=", generated clauses: "+generated_clauses_count;txt+=", kept clauses: "+kept_clauses_count;trace_list.push(txt);if(result){result_model=[];for(i=0;i<varvals.length;i++){if(varvals[i]!==0)result_model.push(showvar(i*varvals[i]));}
if(result_model.length==0)result_model=true;return[result_model,trace_list.join("\r\n")];}
else{return[false,trace_list.join("\r\n")];}}
function store_to_varvals(lit,varvals){if(lit<0)varvals[0-lit]=-1;else varvals[lit]=1;}
function store_to_usable(clause,usable_clauses){if(clause.length<100)usable_clauses[clause.length].push(clause);else usable_clauses[99].push(clause);}
function store_to_processed(clause,processed_clauses,posbuckets,negbuckets){var lit,bucket,nr;lit=clause[0];if(lit<0)negbuckets[0-lit].push(clause);else posbuckets[lit].push(clause);processed_clauses.push(clause);}
function pick_selected(usable_clauses){var bucket,i;for(i=1;i<100;i++){bucket=usable_clauses[i];if(bucket.length>0)return usable_clauses[i].shift();}
return false;}
function tautology(c){var i,j,l,nl;for(i=1;i<c.length;i++){l=c[i];nl=0-l;for(j=0;j<i;j++){if(c[j]===nl)return true;}}
return false;}
function ordered_subsumed(c1,c2){var i,j,lit,found;if(c1.length>c2.length)return false;j=0;for(i=0;i<c1.length;i++){lit=c1[i];found=false;for(;j<c2.length&&c2[j]<=lit;j++){if(c2[j]===lit){found=true;j++;break;}}
if(!found)return false;}
return true;}
function pre_preprocess_clause(clause,varvals,processed_clauses,tmp_array){var j,i,lit,lastlit,s,vn,p,processed,k,found;j=0;lastlit=0;for(i=0;i<clause.length;i++){lit=clause[i];if(lit==lastlit)continue;if(lit<0){s=-1;vn=0-lit}
else{s=1;vn=lit}
if(varvals[vn]!==0){if(varvals[vn]===s){if(clause.length>1)return true;else tmp_array[j++]=lit;}}else{tmp_array[j++]=lit;}
lastlit=lit;}
if(j===0)return false;for(p=0;p<processed_clauses.length;p++){processed=processed_clauses[p];if(processed.length<=j){k=0;for(i=0;i<processed.length;i++){lit=processed[i];found=false;for(;k<j&&tmp_array[k]<=lit;k++){if(tmp_array[k]===lit){found=true;k++;break;}}
if(!found)break;}
if(found)return true;}}
if(j===clause.length)return clause;clause=new Int32Array(j);for(i=0;i<j;i++)clause[i]=tmp_array[i];return clause;}
function preprocess_clause(clause,varvals,processed_clauses,posbuckets,negbuckets,tmp_array){var j,i,k,r,lit,lastlit,s,vn,p,processed,found,bucket;j=0;lastlit=0;for(i=0;i<clause.length;i++){lit=clause[i];if(lit==lastlit)continue;if(lit<0){s=-1;vn=0-lit}
else{s=1;vn=lit}
if(varvals[vn]!==0){if(varvals[vn]===s){if(clause.length>1)return true;else tmp_array[j++]=lit;}}else{tmp_array[j++]=lit;}
lastlit=lit;}
if(j===0)return false;for(r=0;r<j;r++){lit=tmp_array[r];if(lit<0){bucket=negbuckets[0-lit];}
else{bucket=posbuckets[lit];}
for(p=0;p<bucket.length;p++){processed=bucket[p];if(processed.length<=j){k=0;for(i=0;i<processed.length;i++){lit=processed[i];found=false;for(;k<j&&tmp_array[k]<=lit;k++){if(tmp_array[k]===lit){found=true;k++;break;}}
if(!found)break;}
if(found)return true;}}}
if(j===clause.length)return clause;clause=new Int32Array(j);for(i=0;i<j;i++)clause[i]=tmp_array[i];return clause;}
function merge_rest(c1,c2,i1,i2,tmp_array,varvals){var c1len,c2varcount,i,j,p,l,nl,sn,lnr,res,rpos,found;c1len=c1.length;c2varcount=0;for(i=0;i<c2.length;i++){if(i===i2)continue;l=c2[i];nl=(0-l);if(l<0){sn=-1;lnr=nl;}
else{sn=1;lnr=l;}
if(varvals[lnr]!==0){if(varvals[lnr]===sn)return true;continue;}
found=false;for(j=0;j<c1len;j++){if(j===i1)continue;if(c1[j]===l){found=true;break;}
if(c1[j]===nl){return true;}}
if(!found)tmp_array[c2varcount++]=l;}
if(c2varcount===0&&c1len<2)return false;res=new Int32Array((c1len-1)+c2varcount);i=0;j=0;p=0;while(i<c1len&&j<c2varcount){if(i===i1){i++;continue;}
if(c1[i]<=tmp_array[j])res[p++]=c1[i++];else res[p++]=tmp_array[j++];}
for(;i<c1len;i++){if(i!==i1)res[p++]=c1[i];}
for(;j<c2varcount;j++)res[p++]=tmp_array[j];return res;}
function quick_sort_in_place(arr){var stack=[];var left=0;var right=arr.length-1;var i,j,swap,temp;while(true){if(right-left<=25){for(j=left+1;j<=right;j++){swap=arr[j];i=j-1;while(i>=left&&arr[i]>swap){arr[i+1]=arr[i--];}
arr[i+1]=swap;}
if(stack.length==0)break;right=stack.pop();left=stack.pop();}else{var median=(left+right)>>1;i=left+1;j=right;swap=arr[median];arr[median]=arr[i];arr[i]=swap;if(arr[left]>arr[right]){swap=arr[left];arr[left]=arr[right];arr[right]=swap;}if(arr[i]>arr[right]){swap=arr[i];arr[i]=arr[right];arr[right]=swap;}if(arr[left]>arr[i]){swap=arr[left];arr[left]=arr[i];arr[i]=swap;}
temp=arr[i];while(true){do i++;while(arr[i]<temp);do j--;while(arr[j]>temp);if(j<i)break;swap=arr[i];arr[i]=arr[j];arr[j]=swap;}
arr[left+1]=arr[j];arr[j]=temp;if(right-i+1>=j-left){stack.push(i);stack.push(right);right=j-1;}else{stack.push(left);stack.push(j-1);left=i;}}}
return arr;}
function print_trace(depth,txt){var i,s="";if(trace_flag&&trace_method=="console"){for(i=0;i<depth;i++)s+=" ";console.log(s+txt);}else if(trace_flag&&trace_method=="text"){for(i=0;i<depth;i++)s+=" ";trace_list.push(s+txt);}else if(trace_flag&&trace_method=="html"){for(i=0;i<depth;i++)s+="&nbsp;";trace_list.push("<div><tt>"+s+"</tt>"+txt+"</div>");}}
function showvar(x){var nr,sign;if(x&&origvars&&origvars.length>0){if(x<0){nr=0-x;sign="-";}
else{nr=x;sign="";}
if(origvars.length>nr&&origvars[nr])return sign+origvars[nr];else return String(x);}else{return String(x);}}
function clause_to_str(cl){var i,s="";if(cl===true)return"tautology";if(!cl)return"empty";for(i=0;i<cl.length;i++){s+=showvar(cl[i])+" ";}
return s;}})(this.proplog_res={});
