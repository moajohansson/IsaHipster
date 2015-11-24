(*  Author:     Moa Johansson, Chalmers University of Technology

Hipster theory exploration information about what tactic succeeded in a proof attempt.
*)

(*-----------------------------------------------------------------------------------------*)
(* Data recording choises in inductive proofs *)
(*-----------------------------------------------------------------------------------------*)

structure Induction_Data =
struct

datatype T = Data of
  { induction_rule : string option,
    induction_vars : string list, 
    subgoal_tacs_strs : string list
  }

fun get_induction_rule (Data d) = (#induction_rule d)
fun get_induction_vars (Data d) = (#induction_vars d)
fun get_subgoal_tac_strs (Data d) = (#subgoal_tacs_strs d)

fun update_induction_rule f (Data d) = Data{induction_rule = f (#induction_rule d), 
                                       induction_vars = #induction_vars d, 
                                       subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_induction_vars f (Data d) =  Data{induction_rule = #induction_rule d, 
                                       induction_vars = f (#induction_vars d), 
                                       subgoal_tacs_strs = #subgoal_tacs_strs d}
fun update_subgoal_tac_strs f (Data d) = Data{induction_rule = #induction_rule d, 
                                       induction_vars = #induction_vars d, 
                                       subgoal_tacs_strs = f (#subgoal_tacs_strs d)}

fun set_induction_rule rule = update_induction_rule (K rule)
fun set_induction_vars vars = update_induction_vars (K vars)
fun set_subgoal_tac_strs tacs = update_subgoal_tac_strs (K tacs)

fun add_subgoal_tac tac = update_subgoal_tac_strs (fn tacs => tac::tacs)

(* Induction rule NONE defaults to structural induction, as per Isabelle's induction tactic *)
val empty = Data{induction_rule = NONE, induction_vars = [], subgoal_tacs_strs = []}

fun get_proof_script (Data d) = 
  let 

  fun mk_ind_str [] = ""
    | mk_ind_str vars_list = 
      let 
      val vars = String.concatWith " " vars_list
      val induction = "apply (induction " 
      in  
        (case (#induction_rule d) of 
          NONE => induction ^ vars ^ ")\n"
          | SOME rule => induction ^ vars ^ " rule: " ^ rule ^ ")\n")
      end;

  fun mk_app_str [] s = s
    | mk_app_str [t] s = s ^ "by " ^ t
    | mk_app_str (t::ts) s = mk_app_str ts (s ^ "apply " ^ t ^"\n");
    
  in
    (mk_ind_str (#induction_vars d)) ^ (mk_app_str (#subgoal_tacs_strs d) "")
  end;

structure IndData = Proof_Data (type T = T
                                fun init _ = empty)

(* Getting and setting IndDate of a context *)
val induction_rule_of_ctxt = get_induction_rule o IndData.get
val induction_vars_of_ctxt = get_induction_vars o IndData.get
val subgoal_tac_strs_of_ctxt = get_subgoal_tac_strs o IndData.get

fun set_induction_rule_ctxt rule ctxt =
  IndData.put (set_induction_rule rule (IndData.get ctxt)) ctxt
fun set_induction_vars_ctxt vars ctxt =
  IndData.put (set_induction_vars vars (IndData.get ctxt)) ctxt
fun set_subgoal_tac_strs_ctxt tacs ctxt =
  IndData.put (set_subgoal_tac_strs tacs (IndData.get ctxt)) ctxt

fun add_subgoal_tac_ctxt tac ctxt =
  IndData.put (add_subgoal_tac tac (IndData.get ctxt)) ctxt

val reset_ind_proof_data_ctxt = IndData.put empty 

fun get_proof_scrip_ctxt ctxt = get_proof_script (IndData.get ctxt)

end