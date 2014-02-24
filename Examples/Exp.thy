theory Exp
imports "../IsaHipster"

begin

(* The HipSpecifier can't deal with this, as it can't generate Arbitrary instances etc for 
higher-order datatypes like expr *)
(* type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v" *)

datatype ('a,'v, 'b) expr = 
  Cex 'v | 
  Vex 'a | 
  Bex "'b" "('a,'v,'b) expr" "('a,'v,'b) expr"

primrec "value" :: "('b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a,'v,'b) expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" 
where
  "value i (Cex v) env = v" |
  "value i (Vex a) env = env a" |
  "value i (Bex f e1 e2) env = (i f) (value i e1 env) (value i e2 env)"

datatype ('a,'v, 'b) instr = 
  Const 'v
  | Load 'a
  | Apply "'b"

primrec exec :: "('b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a,'v,'b) instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
where
  "exec j [] s vs = vs" |
  "exec j (i#is) s vs = (case i of Const v \<Rightarrow> exec j is s (v#vs)
                                  | Load a \<Rightarrow> exec j is s ((s a)#vs)
                                  | Apply f \<Rightarrow> exec j is s ((j f (hd vs) (hd(tl vs)))#(tl(tl vs))))"


primrec compile :: "('a,'v,'b) expr \<Rightarrow> ('a,'v,'b) instr list" 
  where
  "compile (Cex v) = [Const v]" |
  "compile (Vex a) = [Load a]" |
  "compile (Bex f e1 e2) = (compile e2) @ (compile e1) @ [Apply f]"


ML{*
val consts = ["Exp.value", "Exp.exec", "Exp.compile"];

Hipster_Explore.explore @{context} consts;
*}

end