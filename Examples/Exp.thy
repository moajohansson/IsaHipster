theory Exp
imports Main
uses "HipSpec.ML"

begin

(* The HipSpecifier can't deal with this, as it can't generate instances Arbitrary instances etc for 
higher-order datatypes like expr *)
type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype ('a,'v) expr = 
  Cex 'v | 
  Vex 'a | 
  Bex "'v binop" "('a,'v) expr" "('a,'v) expr"

primrec "value" :: "('a,'v) expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" 
where
  "value (Cex v) env = v" |
  "value (Vex a) env = env a" |
  "value (Bex f e1 e2) env = f (value e1 env) (value e2 env)"

datatype ('a,'v) instr = 
  Const 'v
  | Load 'a
  | Apply "'v binop"

primrec exec :: "('a,'v) instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
where
  "exec [] s vs = vs" |
  "exec (i#is) s vs = (case i of Const v \<Rightarrow> exec is s (v#vs)
                                | Load a \<Rightarrow> exec is s ((s a)#vs)
                                | Apply f \<Rightarrow> exec is s ((f (hd vs) (hd(tl vs)))#(tl(tl vs))))"


primrec compile :: "('a,'v) expr \<Rightarrow> ('a,'v) instr list" 
  where
  "compile (Cex v) = [Const v]" |
  "compile (Vex a) = [Load a]" |
  "compile (Bex f e1 e2) = (compile e2) @ (compile e1) @ [Apply f]"


ML{*
val filepath = "~/TheoremProvers/IsaHip/";
val hipspecifyer_cmd = filepath^"HipSpecifyer";
val modulenm = "Exp";
val consts = map (fn x => modulenm^"."^x) ["value", "exec", "compile"];

HipSpec.hipspec @{theory} hipspecifyer_cmd filepath modulenm consts;
*}

end