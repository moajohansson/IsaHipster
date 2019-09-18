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
  let
    val used_facts = filter_out (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Chained) used_facts0
  in
    if timeout = Time.zeroTime then
      (used_facts, (preferred_meth, Sledgehammer_Proof_Methods.Play_Timed_Out Time.zeroTime))
    else
      let
        val fact_names = map fst used_facts
        val goal_t = Logic.get_goal (Thm.prop_of thm) i
        val _ = Hipster_Utils.maybe_pretty ctxt 60 (Syntax.pretty_term ctxt goal_t)

        fun try_methss [] [] = (used_facts, (preferred_meth, Sledgehammer_Proof_Methods.Play_Timed_Out Time.zeroTime))
          | try_methss ress [] =
            let val _ = 
                        if Misc_Data.verbosity ctxt >= 65 then
                        let val _ = @{print} ("Result",ress) in () end
                        else () in
            (used_facts,
             (case AList.lookup (op =) ress preferred_meth of
               SOME play => (preferred_meth, play)
             | NONE => hd (sort (Sledgehammer_Proof_Methods.play_outcome_ord o apply2 snd) (rev ress))))
            end
          | try_methss ress (meths :: methss) =
            let
              fun is_metis_method (Sledgehammer_Proof_Methods.Metis_Method _) = true
                | is_metis_method _ = false

              fun mk_step fact_names meths =
                Sledgehammer_Isar_Proof.Prove ([], [], ("", 0), goal_t, [], ([], fact_names), meths, "")
             (* val _ = if Misc_Data.verbosity ctxt >= 70 then
                       let val _ = @{print} ("mk_step", mk_step fact_names meths) in () end
                      else () *)
              val ctxt' = Context_Position.set_visible false ctxt
            in
              (case Sledgehammer_Isar_Preplay.preplay_isar_step ctxt' [] timeout [] (mk_step fact_names meths) of
                (* Why only picking first one? It might not make any progress! *)
                (res as (meth, Sledgehammer_Proof_Methods.Played time)) :: more_stuff =>
                let val _ = if Misc_Data.verbosity ctxt >= 70 then
                              let val _ = @{print} ("All results", res::more_stuff) in () end
                            else ()
                    val _ = if Misc_Data.verbosity ctxt >= 70 then
                              let val _ = @{print} ("All facts", fact_names) in () end
                            else ()
                in
                (* if a fact is needed by an ATP, it will be needed by "metis" *)
                if not minimize orelse is_metis_method meth then
                   (used_facts, res) 
                else
                  let
                    val (time', used_names') =
                      Sledgehammer_Isar_Minimize.minimized_isar_step ctxt [] time (mk_step fact_names [meth])
                     ||> (Sledgehammer_Isar_Proof.facts_of_isar_step #> snd)
                      (* Sledgehammer_Isar_Minimize.minimized_isar_step ctxt time (mk_step fact_names [meth])
                      ||> (Sledgehammer_Isar_Proof.facts_of_isar_step #> snd) *)

                    val used_facts' = filter (member (op =) used_names' o fst) used_facts
                  in
                     (used_facts', (meth, Sledgehammer_Proof_Methods.Played time'))
                  end
                end
              | ress' => try_methss (ress' @ ress) methss)
            end
      in
        try_methss [] methss
      end
  end

fun maybe_preplay ctxt thm subgoal (params as {minimize, preplay_timeout,...}) 
                 (result as {outcome, preferred_methss, used_facts, ...}) =
  if Option.isSome outcome then NONE (* Sledgehammer failed to find a proof *) 
  else (* Found a proof, but don't do preplay. *)
    if (preplay_timeout = Time.zeroTime) then SOME (used_facts, fst preferred_methss)
  else (* Do preplay, find suitable method for proof reconstruction. *)
  let
     (* val _ =  @{print} ("Result external prover", result)
     val _ = @{print} ("Facts passed in", used_facts)*)
     val (used_facts', (meth, outcome)) = 
        play_one_line_proof ctxt minimize preplay_timeout used_facts thm subgoal preferred_methss
     (* val _= @{print} (used_facts', meth, outcome) *)
  in
    case outcome of 
    Sledgehammer_Proof_Methods.Played _ => SOME (used_facts',meth)
    | _ => NONE
 end

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
    val learn = mash_learn_proof ctxt params (Thm.prop_of goal) (* (facts) *)
    val prover =  if minimize then get_minimizing_prover ctxt mode learn name params
                 else get_prover ctxt mode name params
    
    val problem =
      (* TODO: In Isabelle2016-1 we have extra "found-proof :: unit \<rightarrow> unit" field. For now identity,
        check what it's used for and where.*)
      {comment = "", state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)], found_proof = I}

  in maybe_preplay ctxt goal i params (prover problem) 
    handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

(* Experiment with good timeouts here. Default is 30s, which is quite a lot.  *) 
fun sledgehammer_get_tac ctxt override_params fact_override chained i th =
  let 
    (* If no minimization of facts is desired, set ("minimize","false") *) 
    val timeout = Misc_Data.sledgehammer_timeout ctxt (* Fetch timeout value for Sledgehammer *)
    val override_params = override_params @ [("preplay_timeout", "0.5"), ("timeout",timeout)]
  in
    (case run_prover override_params fact_override chained i i ctxt th of
      SOME (facts, meth) => 
        let 
        (* NOTE: Problems using this, it's providing faulty proof-strings e.g. "blast some_lemma" 
            instead of "using some_lemma blast) so don't work well with apply style proofs.  *)         
         val (local_fs, global_fs) = 
              List.partition (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Local) 
              (filter_out (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Chained orelse 
                                              sc = ATP_Problem_Generate.Assum) facts);
          (* Hack: Getting the right tactic from Sledgehammer only seem to work if pretending
             that local facts (here things discovered during theory exploration) are in fact 
             Global Facts (normal lemmas from proof script). Might want to write our own alternative
             to this method. *)
          val meth_tac = Sledgehammer_Proof_Methods.tac_of_proof_method ctxt 
                        (* (maps (thms_of_name ctxt o fst) local_fs, *)
                          ([],
                          maps (thms_of_name ctxt o fst) (global_fs@local_fs)) meth 
        in SOME (meth_tac, (meth, map fst facts)) end
    | NONE => NONE (* ([], no_tac, "no_tac")) *)
  handle Fail  msg => (warning ("Failure in: *" ^ msg ^"\n"); NONE))
end;

(* To be used to quickly filter out "routine" lemmas from theory exploration. Doesn't bother
   with proof reconstruction, just trusts the external prover. *) 
fun just_sledgehammer ctxt override_params fact_override chained i th =
  let 
    val override_params = override_params @ [("preplay_timeout","0"), ("timeout","5"),("minimize","false")] 
  in
    (case run_prover override_params fact_override chained i i ctxt th of
      SOME _ => all_tac th
    | NONE => no_tac th)
  handle Fail  msg => (warning ("Failure in: *" ^ msg ^"\n"); no_tac th)
end;

(*
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
*)
end;
