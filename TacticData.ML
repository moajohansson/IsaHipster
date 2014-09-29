(*-----------------------------------------------------------------------------------------*)
(* Data about tactics for hard/routine reasoning used for theory exploration *)
(*-----------------------------------------------------------------------------------------*)

structure Tactic_Data =
struct

datatype T = Data of 
         { routine_tac : Proof.context -> tactic,
           hard_tac : Proof.context -> tactic,
           routine_tac_str : string,     
           hard_tac_str : Proof.context -> string};


fun get_routine_tac (Data d) = (#routine_tac d);
fun get_hard_tac (Data d) = (#hard_tac d);
fun get_routine_str (Data d) = (#routine_tac_str d);
fun get_hard_str (Data d) = (#hard_tac_str d);

(* Dummy data *)
(*val empty = Data{routine_tac = K FAIL, hard_tac = K FAIL, routine_tac_str = "FAIL", 
                 hard_tac_str = fn _ => K "FAIL"}; *)

(* Routine: simplification and FO reasoning. Hard: Induction, then routine. *)
val induct_simp_metis = Data {routine_tac = Simp_Metis_Tacs.routine_tac, 
                              hard_tac = Simp_Metis_Tacs.hard_tac,
                              routine_tac_str = Simp_Metis_Tacs.routine_tac_str, 
                              hard_tac_str = Simp_Metis_Tacs.final_tactic_str};

(* Routine: simplification. Hard: Indution, then simp. *)
val induct_simp = Data {routine_tac = Simp_Tacs.routine_tac, 
                        hard_tac = Simp_Tacs.hard_tac,
                        routine_tac_str = Simp_Tacs.routine_tac_str, 
                        hard_tac_str = Simp_Tacs.final_tactic_str};


(* Data stored in an Isabelle context, default to induct_simp_metis tactics. 
   THINK: Maybe theis should be stored in the theory instead? *)
structure Data = Theory_Data 
                   (type T = T
                   val empty = induct_simp_metis (* Default tactics *)
                   val extend = I
                   val merge = fst)

fun routine_tac ctxt = (get_routine_tac (Data.get (Proof_Context.theory_of ctxt))) ctxt;
fun hard_tac ctxt = (get_hard_tac (Data.get (Proof_Context.theory_of ctxt))) ctxt;
fun hard_tac_str ctxt = (get_hard_str (Data.get (Proof_Context.theory_of ctxt))) ctxt;
val routine_tac_str = get_routine_str o (Data.get o Proof_Context.theory_of);

val set_tacs = Data.put;
val set_induct_simp_metis = set_tacs induct_simp_metis;
val set_induct_simp = set_tacs induct_simp;

end;
