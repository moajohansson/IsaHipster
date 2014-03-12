theory Exp
imports "../IsaHipster"

begin

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype ('c, 'v) expr =
  Cex 'c |
  Vex 'v |
  Bex "'v binop" "('c,'v) expr" "('c,'v) expr"

fun "value" :: "('v \<Rightarrow> 'c) \<Rightarrow> ('c,'v) expr \<Rightarrow> 'c"
where
  "value env (Cex c) = c" |
  "value env (Vex v) = env v" |
  "value env (Bex b e1 e2) = b (value env e1) (value env e2)"

datatype ('c, 'v, 'b) program =
  Done
  | Const 'c "('c, 'v, 'b) program"
  | Load 'v "('c, 'v, 'b) program"
  | Apply 'b "('c, 'v, 'b) program"

fun sequence :: "('c, 'v, 'b) program => ('c, 'v, 'b) program => ('c, 'v, 'b) program"
where
  "sequence Done p = p"
  | "sequence (Const c p) p' = Const c (sequence p p')"
  | "sequence (Load v p) p' = Load v (sequence p p')"
  | "sequence (Apply b p) p' = Apply b (sequence p p')" 

fun exec :: "('v \<Rightarrow> 'c) \<Rightarrow>  ('c,'v) program \<Rightarrow> 'c list \<Rightarrow> 'c list"
where
  "exec env Done stack = stack"
  | "exec env (Const c p) stack = exec env p (c#stack)"
  | "exec env (Load v p) stack = exec env p ((env v)#stack)"
  | "exec env (Apply b p) stack =
     exec env p ((b (hd stack) (hd(tl stack)))#(tl(tl stack)))"

fun compile :: "('c,'v) expr \<Rightarrow> ('c,'v) program"
  where
  "compile (Cex c) =  Const c Done" |
  "compile (Vex v) =  Load v Done" |
  "compile (Bex b e1 e2) = sequence (compile e2) (sequence (compile e1) (Apply b Done))"

ML{*
val consts = ["Exp.value", "Exp.exec", "Exp.compile", "Exp.sequence"];

Hipster_Explore.explore @{context} consts;

*}


lemma lemma_a [thy_expl]: "sequence x4 Done = x4"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "exec x4 y4 (sequence z4 x14) xs4 = exec x4 y4 x14 (exec x4 y4 z4 xs4)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps thy_expl} *})

lemma lemma_ab [thy_expl]: "exec x3 y3 (compile z3) xs3 = value x3 y3 z3 # xs3"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps thy_expl} *})

theorem our_thm : "exec getBinop env (compile e) [] = [value getBinop env e]"
sledgehammer
by (metis lemma_ab)

(*
(* First try by user, gets stuck, call theory exploration, get suitable lemmas. After can prove goal
by Sledgehammering *)
apply (induct e)
apply (simp_all)
apply (tactic {*Hipster_Explore.explore_goal @{context} consts*})
 
*)


end