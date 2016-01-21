(* Copied from Isabelle's Sledgehammer_Tactics to avoid hiding behind signature *)

structure Hipster_Sledgehammer_Tactics  =
struct

open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh
open Sledgehammer_Commands

fun run_prover override_params fact_override chained i n ctxt goal =
  let
    val thy = Proof_Context.theory_of ctxt
    val mode = Normal
    val params as {provers, max_facts, ...} = default_params thy override_params
    val name = hd provers
    val prover = get_prover ctxt mode name
    val default_max_facts = default_max_facts_of_prover ctxt name
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal i ctxt
    val ho_atp = exists (is_ho_atp ctxt) provers
    val keywords = Thy_Header.get_keywords' ctxt
    val css_table = clasimpset_rule_table_of ctxt
    val facts =
      nearly_all_facts ctxt ho_atp fact_override keywords css_table chained hyp_ts concl_t
      |> relevant_facts ctxt params name (the_default default_max_facts max_facts) fact_override
        hyp_ts concl_t
      |> hd |> snd
    val problem =
      {comment = "", state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)]}
  in
    (case prover params problem of
      {outcome = NONE, used_facts, ...} => used_facts |> map fst |> SOME
    | _ => NONE)
    handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

(* Tactic to call during theory exploration. Return facts sledgehammer finds,
   so we can paste in the relevant ones into the proof script later *)
fun sledgehammer_with_metis_tac ctxt override_params fact_override chained i thm =
  let 
    val override_params = override_params @ [("preplay_timeout", "0")] 
    in
    (case run_prover override_params fact_override chained i i ctxt thm of
      SOME facts =>
      (facts, (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combs_or_liftingN ctxt
          (maps (thms_of_name ctxt) facts) i))
    | NONE => ([],no_tac))
  end

fun sledgehammer_with_metis_all_goals ctxt override_params fact_override chained  th =
  let
    fun MAP_THEN [] = all_tac
      | MAP_THEN (t::tacs) = t THEN (MAP_THEN tacs)

    fun repeate 0 facts tacs thm = (facts, MAP_THEN tacs)
      | repeate n facts tacs thm = 
        let val (more_fs, tac2) = 
          sledgehammer_with_metis_tac ctxt override_params fact_override chained n thm
        in repeate (n-1) (facts@more_fs) (tacs@[tac2]) thm end
  in 
    repeate (*(sledgehammer_with_metis_tac ctxt override_params fact_override chained)*)
            (Thm.nprems_of th) [] [] th
  end

end;
