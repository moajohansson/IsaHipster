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
    hard_ctac : CTac.ctactic,
    hard_tac_str : Proof.context -> string, 
    applies_to : Proof.context -> Thm.thm -> bool }


fun get_technique (Data d) = (#technique d)
fun get_routine_tac (Data d) = (#routine_tac d)
fun get_hard_ctac (Data d) = (#hard_ctac d)
fun get_hard_str (Data d) = (#hard_tac_str d)
fun get_applies_to (Data d) = (#applies_to d)

fun has_technique s dl = exists (curry op = s o get_technique) dl
fun get_data s dl = find_first (curry op = s o get_technique) dl

(* FIXME: Please move this to the relevant tactic.*)
fun coind_recognizer ctxt c = not(null(Hipster_Utils.coinductible_types (Thm.concl_of c) ctxt))
fun ind_recognizer ctxt c = not(null(Hipster_Utils.inductible_types (Thm.concl_of c) ctxt))
(* Dummy data *)
(*val empty = Data{routine_tac = K FAIL, hard_tac = K FAIL,
                routine_tac_str = "FAIL", hard_tac_str = fn _ => K "FAIL"}; *)


(* Routine: simplification and FO reasoning. Hard: Induction, then routine. *)
 (*val induct_with_schemes = Data {technique = "induction",
                                routine_tac = Ind_Schemes_T.routine_tac,
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac_rec,
                                hard_tac_str = Ind_Schemes_T.final_tactic_str, 
                                applies_to = ind_recognizer} *)

(* Routine: simplification and FO reasoning. Hard: Induction, then routine. *)
(* val induct_simp_metis = Data {technique = "induction",
                                 routine_tac = Simp_Metis_T.routine_tac,
                                 hard_tac = Simp_Metis_T.hard_tac,
                                 hard_ctac = Induct_CTac.thy_expl_hard_ctac_,
                                 routine_tac_str = Simp_Metis_T.routine_tac_str,
                                 hard_tac_str = Simp_Metis_T.final_tactic_str,
                                 applies_to = ind_recognizer} *)
(*
val recursion_induction =  Data {technique = "recursion induction",
                                 routine_tac = Rec_Ind_T.routine_tac,
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac_rec,
                                hard_tac_str = Rec_Ind_T.final_tactic_str, 
                                applies_to = ind_recognizer}
*)
(* Routine: simplification. Hard: Structural Induction, then simp. *)
val induct_simp = Data {technique = "induction",
                        routine_tac = fn ctxt =>
                          let val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
                          in
                            SOLVE (Ind_Tacs.prove_by_simp ctxt lemmas)
                          end,
                        hard_ctac = Induct_CTac.thy_expl_hard_ctac_simp_struct,
                        hard_tac_str = Induction_Data.get_proof_script_ctxt, 
                        applies_to = ind_recognizer}

(* Sledgehammer, or sledgehammer + structural induction or recursion induction *)
val induct_sledgehammer = Data {technique = "induction",
                                routine_tac = (fn ctxt => fn thm =>
                                  let
                                    val proved = ThyExpl_Data.proved_of_ctxt ctxt
                                    in
                                      ALLGOALS (Hipster_Sledgehammer_Tactics.just_sledgehammer ctxt []
                                        Sledgehammer_Fact.no_fact_override proved) thm
                                    end),                          
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac_struct_or_rec,
                                hard_tac_str = Induction_Data.get_proof_script_ctxt,
                                applies_to = ind_recognizer}

val recinduct_sledgehammer = Data {technique = "induction",
                                routine_tac = (fn ctxt => fn thm =>
                                  let
                                    val proved = ThyExpl_Data.proved_of_ctxt ctxt
                                    in
                                      ALLGOALS (Hipster_Sledgehammer_Tactics.just_sledgehammer ctxt []
                                        Sledgehammer_Fact.no_fact_override proved) thm
                                    end),                          
                                hard_ctac = Induct_CTac.thy_expl_hard_ctac_rec,
                                hard_tac_str = Induction_Data.get_proof_script_ctxt,
                                applies_to = ind_recognizer}

val coinduct_sledgehammer = Data {technique = "coinduction",
                                  routine_tac = Coinduct_T.routine_tac,
                                  hard_ctac = Coinduct_CTac.thy_expl_coind_ctac,
                                  hard_tac_str = Coinduction_Data.get_proof_script_ctxt, 
                                  applies_to = coind_recognizer}

val coinduct_sledgehammer_auto = Data {technique = "coinduction",
                                  routine_tac = SOLVE o Clasimp.auto_tac,
                                  hard_ctac = Coinduct_CTac.thy_expl_coind_ctac,
                                  hard_tac_str = Coinduction_Data.get_proof_script_ctxt,
                                  applies_to = coind_recognizer}

val sledgehammer_coinduct = Data {technique = "coinduction",
                                  routine_tac = Coinduct_T.routine_tac,
                                  hard_ctac = Coinduct_CTac.thy_expl_sledge_or_coind_ctac,
                                  hard_tac_str = Coinduction_Data.get_proof_script_ctxt, 
                                  applies_to = coind_recognizer}
(* Dummy tactic data for theory exploration. Doens't prove anything, just outputs stuff from QuickSpec *)
val no_proof = Data {technique = "Just explore, no proofs",
                                  routine_tac = K no_tac,
                                  hard_ctac = CTac.no_ctac,
                                  hard_tac_str = K "oops", 
                                  applies_to = K o K true}

(* Routine: simp, Hard: Sledgehammer orelse Induction + Sledgehammer *)
(*val simp_sledgehammer_induct_sledgehammer = Data {technique = "induction",
                                                  routine_tac = Simp_T.routine_tac,
                                                  hard_ctac = Induct_CTac.thy_expl_hard_sledge_or_struct,
                                                  hard_tac_str = Sledgehammer_T.final_tactic_str,
                                                  applies_to = ind_recognizer}  (* Redundant *)
*)

structure Data = Theory_Data
  ( type T = T
    val empty = induct_sledgehammer (* induct_with_schemes *)(* Default tactics *)
    val extend = I
    val merge = fst )

fun routine_tac ctxt = (get_routine_tac) (Data.get (Proof_Context.theory_of ctxt)) ctxt
fun hard_ctac ctxt = (get_hard_ctac) (Data.get (Proof_Context.theory_of ctxt))
fun hard_tac_str ctxt = (get_hard_str) (Data.get (Proof_Context.theory_of ctxt)) ctxt 

(*val techniques = map get_technique o (Data.get o Proof_Context.theory_of)
fun default_technique ctxt = (get_technique o hd o (Data.get o Proof_Context.theory_of)) ctxt
*)

val set_tacs = Data.put
val get_tacs = Data.get
val set_induct_simp = set_tacs induct_simp
val set_induct_sledgehammer = set_tacs induct_sledgehammer
val set_recinduct_sledgehammer =  set_tacs recinduct_sledgehammer
(*val set_coinduct_sledgehammer = set_tacs [induct_sledgehammer,coinduct_sledgehammer]
val set_sledgehammer_coinduct = set_tacs [induct_sledgehammer,sledgehammer_coinduct]*)

(* val set_sledge_induct_sledge = set_tacs [simp_sledgehammer_induct_sledgehammer] *)
val set_no_proof = set_tacs no_proof
(* val set_coinduct_sledgehammer_auto = set_tacs [induct_sledgehammer,coinduct_sledgehammer_auto] *)

end
