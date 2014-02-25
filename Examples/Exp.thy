theory Exp
imports "../IsaHipster"

begin

(* The HipSpecifier can't deal with this, as it can't generate Arbitrary instances etc for
higher-order datatypes like expr *)
(* type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v" *)

datatype ('a, 'v, 'b) expr =
  Cex 'v |
  Vex 'a |
  Bex "'b" "('a,'v,'b) expr" "('a,'v,'b) expr"

primrec "value" :: "('b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a,'v,'b) expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v"
where
  "value i (Cex v) env = v" |
  "value i (Vex a) env = env a" |
  "value i (Bex f e1 e2) env = (i f) (value i e1 env) (value i e2 env)"

datatype ('a, 'v, 'b) instr =
  Const 'v
  | Load 'a
  | Apply "'b"

datatype ('a, 'v, 'b) instr_list =
  Instr_nil
  | Instr_cons "('a, 'v, 'b) instr" "('a, 'v, 'b) instr_list"

primrec instr_app :: "('a, 'v, 'b) instr_list => ('a, 'v, 'b) instr_list => ('a, 'v, 'b) instr_list"
where
  "instr_app Instr_nil xs = xs"
| "instr_app (Instr_cons x xs) ys = Instr_cons x (instr_app xs ys)"

primrec exec :: "('b \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a,'v,'b) instr_list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
where
  "exec j Instr_nil s vs = vs" |
  "exec j (Instr_cons i is) s vs =
    (case i of Const v \<Rightarrow> exec j is s (v#vs)
             | Load a \<Rightarrow> exec j is s ((s a)#vs)
             | Apply f \<Rightarrow> exec j is s ((j f (hd vs) (hd(tl vs)))#(tl(tl vs))))"


primrec compile :: "('a,'v,'b) expr \<Rightarrow> ('a,'v,'b) instr_list"
  where
  "compile (Cex v) = Instr_cons (Const v) Instr_nil" |
  "compile (Vex a) = Instr_cons (Load a) Instr_nil" |
  "compile (Bex f e1 e2) = instr_app (compile e2) (instr_app (compile e1) (Instr_cons (Apply f) Instr_nil))"


ML{*
val consts = ["Exp.value", "Exp.exec", "Exp.compile"];

Hipster_Explore.explore @{context} consts;
*}

end