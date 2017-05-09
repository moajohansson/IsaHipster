(*  Author:     Moa Johansson, Chalmers University of Technology
    Author:     Irene Lobo Valbuena, Chalmers University of Technology

Hipster theory exploration reasoning parameterisation.
*)

(*-----------------------------------------------------------------------------------------*)
(* Data about tactics for hard/routine reasoning used for theory exploration *)
(*-----------------------------------------------------------------------------------------*)

structure Tactic_Data =
struct

datatype T = Data of
  { technique : string,
    routine_tac : Proof.context -> tactic,
    hard_tac : Proof.context ->  tactic,
    hard_ctac : CTac.ctactic,
    routine_tac_str : string,
    hard_tac_str : Proof.context -> string }


fun get_technique (Data d) = (#technique d)
fun get_routine_tac (Data d) = (#routine_tac d)
fun get_hard_tac (Data d) = (#hard_tac d)
fun get_hard_ctac (Data d) = (#hard_ctac d)
fun get_routine_str (Data d) = (#routine_tac_str d)
fun get_hard_str (Data d) = (#hard_tac_str d)

(* Dummy data *)
(*val empty = Data{routine_tac = K FAIL, hard_tac = K FAIL,
                routine_tac_str = "FAIL", hard_tac_str = fn _ => K "FAIL"}; *)

(* Work in progress: All the below has the same hard_ctac right now. This is what's used by
   Hipster during exploration, and obviously due to change.
 *)
(* Routine: simplification and FO reasoning. Hard: Induction, then routine. *)
val induct_with_schemes = Data {technique = "induction",
                                routine_tac = Ind_Schemes_T.routine_tac,
                                hard_tac = Ind_Schemes_T.hard_tac,
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac,
                                routine_tac_str = Ind_Schemes_T.routine_tac_str,
                                hard_tac_str = Ind_Schemes_T.final_tactic_str}

(* Routine: simplification and FO reasoning. Hard: Induction, then routine. *)
val induct_simp_metis = Data {technique = "induction",
                              routine_tac = Simp_Metis_T.routine_tac,
                              hard_tac = Simp_Metis_T.hard_tac,
                              hard_ctac = Induct_CTac.thy_expl_hard_ctac,
                              routine_tac_str = Simp_Metis_T.routine_tac_str,
                              hard_tac_str = Simp_Metis_T.final_tactic_str}

(* Routine: simplification. Hard: Induction, then simp. *)
val induct_simp = Data {technique = "induction",
                        routine_tac = Simp_T.routine_tac,
                        hard_tac = Simp_T.hard_tac,
                        hard_ctac = Induct_CTac.thy_expl_hard_ctac,
                        routine_tac_str = Simp_T.routine_tac_str,
                        hard_tac_str = Simp_T.final_tactic_str}

(* Sledgehammer, or sledgehammer + induction *)
val induct_sledgehammer = Data {technique = "induction",
                                routine_tac = Sledgehammer_T.routine_tac,
                                hard_tac = Sledgehammer_T.hard_tac,
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac,
                                routine_tac_str = Sledgehammer_T.routine_tac_str,
                                hard_tac_str = Sledgehammer_T.final_tactic_str}

val coinduct_sledgehammer = Data {technique = "coinduction",
                                  routine_tac = Coinduct_T.routine_tac,
                                  hard_tac = Coinduct_T.hard_tac,
                                  hard_ctac = Coinduct_CTac.thy_expl_coind_ctac,
                                  routine_tac_str = Coinduct_T.routine_tac_str,
                                  hard_tac_str = Coinduct_T.final_tactic_str}

(* Data stored in an Isabelle context, default to induct_with_schemes tactics.
   THINK: Maybe this should be stored in the theory instead? *)
structure Data = Theory_Data
  ( type T = T
    val empty = induct_sledgehammer(* induct_with_schemes *)(* Default tactics *)
    val extend = I
    val merge = fst )

fun routine_tac ctxt = (get_routine_tac (Data.get (Proof_Context.theory_of ctxt))) ctxt
fun hard_tac ctxt = (get_hard_tac (Data.get (Proof_Context.theory_of ctxt))) ctxt
fun hard_ctac ctxt = get_hard_ctac (Data.get (Proof_Context.theory_of ctxt))
fun hard_tac_str ctxt = (get_hard_str (Data.get (Proof_Context.theory_of ctxt))) ctxt
val routine_tac_str = get_routine_str o (Data.get o Proof_Context.theory_of)
val technique = get_technique o (Data.get o Proof_Context.theory_of)

val set_tacs = Data.put
val set_induct_simp_metis = set_tacs induct_simp_metis
val set_induct_simp = set_tacs induct_simp
val set_induct_with_schemes = set_tacs induct_with_schemes
val set_induct_sledgehammer = set_tacs induct_sledgehammer
val set_coinduct_sledgehammer = set_tacs coinduct_sledgehammer

end
