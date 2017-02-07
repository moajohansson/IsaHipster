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

(* If parameter minimize is true (default) tries to minimise the list of facts from the external prover,
   i.e. it removes redundant ones to create nicer proofs. Takes a bit longer, but avoids 
   proofs that have extra facts in them. *)
fun run_prover override_params fact_override chained i n ctxt goal =
  let
    val thy = Proof_Context.theory_of ctxt
    val mode = Normal 
    val params as {provers, max_facts, minimize, ...} = default_params thy override_params
    val name = hd provers
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

    (* Check if the prover should minimize (remove redundant facts) or not*)
    val learn = mash_learn_proof ctxt params (Thm.prop_of goal) facts
    val prover = if minimize then get_minimizing_prover ctxt mode learn name params
                 else get_prover ctxt mode name params
    
    val problem =
      {comment = "", state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)]}
  in
   (case prover problem of (* This is of type Sledgehammer_Prover.prover_result*)
      {outcome = NONE, used_facts,...} => 
      (*let val _ = @{print} (preferred_methss) in *)
      used_facts |> map fst |> SOME
    | _ => NONE) 
    handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

(* Experiment with good timeouts here. Default is 30s, which is quite a lot.  *) 
fun sledgehammer_with_metis_tac ctxt override_params fact_override chained i th =
  let 
    (* If no minimization of facts is desired, set ("minimize","false") *) 
    val override_params = override_params @ [("preplay_timeout", "0"), ("timeout","10")] 
  in
    (case run_prover override_params fact_override chained i i ctxt th of
      SOME facts => 
      let val (ffss, m) =
        (facts, (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combs_or_liftingN ctxt
            (maps (thms_of_name ctxt) facts) i))
          in (ffss, m) end
    | NONE => ([],no_tac))
  handle Fail  msg => (warning ("Failure in: *" ^ msg ^"\n"); ([], no_tac))
end;

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
