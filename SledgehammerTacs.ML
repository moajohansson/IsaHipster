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

(* Modified version of Sledgehammer.play_one_line_proof, which tries to reconstruct an ATP/SMT 
   proof in Isabelle using various methods (avoids some Isar specific stuff). *)
fun play_one_line_proof ctxt minimize timeout used_facts0 thm i (preferred_meth, methss) =
  let val used_facts = filter_out (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Chained) used_facts0 in
    if timeout = Time.zeroTime then
      (used_facts, (preferred_meth, Sledgehammer_Proof_Methods.Play_Timed_Out Time.zeroTime))
    else
      let
        val fact_names = map fst used_facts
        val goal_t = Logic.get_goal (Thm.prop_of thm) i

        fun try_methss [] [] = (used_facts, (preferred_meth, Sledgehammer_Proof_Methods.Play_Timed_Out Time.zeroTime))
          | try_methss ress [] =
            (used_facts,
             (case AList.lookup (op =) ress preferred_meth of
               SOME play => (preferred_meth, play)
             | NONE => hd (sort (Sledgehammer_Proof_Methods.play_outcome_ord o apply2 snd) (rev ress))))
          | try_methss ress (meths :: methss) =
            let

              fun is_metis_method (Sledgehammer_Proof_Methods.Metis_Method _) = true
                | is_metis_method _ = false

              fun mk_step fact_names meths =
                Sledgehammer_Isar_Proof.Prove ([], [], ("", 0), goal_t, [], ([], fact_names), meths, "")
              
              val chained = [];
            in
              (case Sledgehammer_Isar_Preplay.preplay_isar_step ctxt chained timeout [] (mk_step fact_names meths) of
                (res as (meth, Sledgehammer_Proof_Methods.Played time)) :: _ =>
                (* if a fact is needed by an ATP, it will be needed by "metis" *)
                if not minimize orelse is_metis_method meth then
                  (used_facts, res)
                else
                  let
                    val (time', used_names') =
                       Sledgehammer_Isar_Minimize.minimized_isar_step ctxt time (mk_step fact_names [meth])
                      ||> (Sledgehammer_Isar_Proof.facts_of_isar_step #> snd)
                    val used_facts' = filter (member (op =) used_names' o fst) used_facts
                  in
                    (used_facts', (meth, Sledgehammer_Proof_Methods.Played time'))
                  end
              | ress' => try_methss (ress' @ ress) methss)
            end
      in
        try_methss [] methss
      end
  end

fun test_preplay ctxt thm subgoal (params as {minimize, timeout,...} ) 
                 (result as {preferred_methss, used_facts, ...}) =
  let
     val x = play_one_line_proof ctxt minimize timeout used_facts thm subgoal preferred_methss
     val _ =  @{print} x
     in result end
 
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

    val result = test_preplay ctxt goal i params (prover problem) 

  in
   (case result (*prover problem*) of (* This is of type Sledgehammer_Prover.prover_result*)
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
    val override_params = override_params @ [("preplay_timeout", "0.5"), ("timeout","10")] 
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
