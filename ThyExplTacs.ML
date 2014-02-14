(* Structure for parametrising theory exploration. Defines easy "routine" reasoning
and what is considered "hard" reasoning. Theory exploration will discard stuff that
follows only from routine reasoning and keep interesting theorems that required "hard"
reasoning. *)

signature THY_EXPL_TACS =
sig
  val routine_tac : Proof.context -> tactic
  val hard_tac : Proof.context -> tactic
  val final_tactic_str : Proof.context -> string list -> string
end


(* This structure considers simplification or FO reasoning by Metis as routine. *)
(* Proofs requiring structural induction is considered as "hard"                *)
structure Simp_Metis_Tacs : THY_EXPL_TACS =
struct

fun routine_tac ctxt = 
     let
       val prev_thms = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
       val ss = Library.foldl (fn (ss,thm) => Simplifier.add_simp thm ss)
                                  (Simplifier.simpset_of ctxt, prev_thms)
     in
       Hipster_Tacs.simp_or_metis ctxt ss (prev_thms @ (ThyExpl_Data.facts_of_ctxt ctxt))
     end; 

fun hard_tac ctxt = 
    let
      val prev_thms = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
      val ss = Library.foldl (fn (ss,thm) => Simplifier.add_simp thm ss)
                                  (Simplifier.simpset_of ctxt, prev_thms)
    in
      ALLGOALS (Hipster_Tacs.try_inductable_vars ctxt ss 
                                                 (prev_thms @ (ThyExpl_Data.facts_of_ctxt ctxt)))
    end; 

(* The fact_nms are names of extra theorems that we want to refer to in the output *)
fun final_tactic_str _ fact_nms =
    let
      val facts_str = "@{thms "^ (Library.space_implode " " fact_nms) ^ " thy_expl}" 
    in 
      "by (tactic {* Hipster_Tacs.induct_simp_metis @{context} " 
      ^ facts_str ^" *})"
    end;
end


