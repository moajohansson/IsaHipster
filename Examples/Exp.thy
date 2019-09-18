theory Exp
imports "$HIPSTER_HOME/IsaHipster"

begin

type_synonym 'c binop = "'c \<Rightarrow> 'c \<Rightarrow> 'c"

datatype ('c, 'v) expr =
  Cex 'c |
  Vex 'v |
  Bex "'c binop" "('c,'v) expr" "('c,'v) expr"

fun "value" :: "('v \<Rightarrow> 'c) \<Rightarrow> ('c,'v) expr \<Rightarrow> 'c"
where
  "value env (Cex c) = c" |
  "value env (Vex v) = env v" |
  "value env (Bex b e1 e2) = b (value env e1) (value env e2)"

datatype ('c, 'v) program =
  Done
  | Const 'c "('c, 'v) program"
  | Load 'v "('c, 'v) program"
  | Apply "'c binop" "('c, 'v) program"

fun sequence :: "('c, 'v) program => ('c, 'v) program => ('c, 'v) program"
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
hipster exec
(*
hipster value exec compile sequence
*)
(*
lemma lemma_a [thy_expl]: "sequence x4 Done = x4"
by (hipster_induct_simp_metis Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps)

lemma lemma_aa [thy_expl]: "exec x4 (sequence y4 z4) xs4 = exec x4 z4 (exec x4 y4 xs4)"
by (hipster_induct_simp_metis Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps)

lemma lemma_ab [thy_expl]: "exec x3 (compile y3) xs3 = value x3 y3 # xs3"
by (hipster_induct_simp_metis Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps)

lemma lemma_ac [thy_expl]: "sequence (sequence x4 y4) z4 = sequence x4 (sequence y4 z4)"
by (hipster_induct_simp_metis Exp.value.simps Exp.exec.simps Exp.compile.simps Exp.sequence.simps)
*)
ML\<open>Tactic_Data.routine_tac_str @{context};\<close> 
theorem our_thm : "exec env (compile e) [] = [value  env e]"
(*apply (tactic {* Tactic_Data.routine_tac @{context}*}) *)

apply (tactic \<open>Hipster_Explore.explore_goal @{context} ["Exp.compile", "Exp.exec", "Exp.value"]\<close>)
(*
sledgehammer
by (metis lemma_ab)
*)

end
