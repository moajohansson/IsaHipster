(*  Author:     Moa Johansson, Chalmers University of Technology

Hipster theory exploration information about what tactic suceeded in a proof attempt.
*)

(*-----------------------------------------------------------------------------------------*)
(*-----------------------------------------------------------------------------------------*)

structure Proof_Data =
struct

datatype T = Data of
  { induction_tac : (tactic * string) option,
    induction_vars : string list, 
    subgoal_tacs_strs : string list ,
  }

fun get_induction_tac (Data d) = (#induction_tac d)
fun get_induction_vars (Data d) = (#induction_vars d)
fun get_subgoal_tac_strs (Data d) = (#subgoal_tac_strs d)

val empty = Data{induction_tac = NONE, induction_vars = [], subgoals_tacs_strs = []}

(* TODO: FINISH, see ThyExplData for examples *)
structure ProofData = Data (type T = T
                            fun init _ = empty)


end