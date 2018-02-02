(*  Author:     Solrun Einarsdottir, Chalmers University of Technology *)

(* Contextual tactic for coinduction, much is borrowed from InductCTac.ML *)

signature COINDUCT_CTAC =
sig

val thy_expl_coind_ctac : CTac.ctactic
val thy_expl_sledge_or_coind_ctac : CTac.ctactic

end

structure Coinduct_CTac  : COINDUCT_CTAC   =
struct
(* Apply coinduction and record which rule was used, and which variables were arbitrary *)
fun coinduct_with_arb_ctac rule vars (ctxt,thm) =
  let val typename = hd (Hipster_Utils.type_names (Thm.concl_of thm))
      val _ = Hipster_Utils.maybe_print ctxt 100 ("Strong coinduction on type: " ^ typename)
      val rulename = typename ^ ".coinduct_strong"
      val rule' = case rule of SOME (_,thms) => SOME thms
                               | NONE => SOME [(Proof_Context.get_thm ctxt rulename)]
      val results = HEADGOAL(Coinduction.coinduction_tac ctxt vars rule' []) thm
      fun set_rule r  = case r of NONE =>
                        Coinduction_Data.set_coinduction_rule_ctxt (SOME rulename)
                                | SOME (nm,_) =>
                        Coinduction_Data.set_coinduction_rule_ctxt (SOME nm)
  in
    Seq.map (fn thm' =>
      (ctxt
       |> Coinduction_Data.set_arbitrary_vars_ctxt (map fst (map Term.dest_Free vars))
       |> set_rule rule, thm')) results
  end;

(* Apply coinduction and record which rule was used, and which variables were arbitrary *)
fun coinduct_upto_with_arb_ctac rule vars (ctxt,thm) =
  let val const_names = Hipster_Utils.thy_consts_of ""(*TODO: empty string should be current theory name*) thm
      val rulenames = map (fn x => x ^ ".coinduct") const_names |>
                      filter (can (Proof_Context.get_thm ctxt))
  in case rulenames of
          [] => Seq.empty
        | rulename::_ =>
          let
            val _ = Hipster_Utils.maybe_print ctxt 100 ("Using coinduction rule: " ^ rulename)
            val rule' = SOME [(Proof_Context.get_thm ctxt rulename)]
            val results = HEADGOAL(Coinduction.coinduction_tac ctxt [](*vars*) rule' []) thm
    in
      Seq.map (fn thm' =>
        (ctxt
         |> Coinduction_Data.set_arbitrary_vars_ctxt (map fst (map Term.dest_Free [](*vars*)))
         |> Coinduction_Data.set_coinduction_rule_ctxt (SOME rulename), thm')) results
    end
  end;

fun coinduct_allfree_arbitrary_ctac rule (ctxt,thm) =
  let val t = Thm.concl_of thm
      val fvs = Hipster_Utils.add_term_frees(t, [])
  in
    coinduct_with_arb_ctac rule fvs (ctxt,thm)
  end;

fun coinduct_upto_allfree_arbitrary_ctac rule (ctxt,thm) =
  let val t = Thm.concl_of thm
      val fvs = Hipster_Utils.add_term_frees(t, [])
  in
    coinduct_upto_with_arb_ctac rule fvs (ctxt,thm)
  end;

fun simp_goal_ctac i (ctxt,thm) =
  Seq.map
    (fn (ctxt',thm') => (Coinduction_Data.add_subgoal_tac_ctxt
                        (i, (Induction_Data.Sledgehammer_Meth Sledgehammer_Proof_Methods.Simp_Method, []))
                        ctxt',thm'))
     (CTac.AS_CTACTIC (CHANGED (Simplifier.asm_full_simp_tac ctxt i)) (ctxt,thm))

fun simp_no_goal_ctac i =
  CTac.CORELSE(CTac.SOLVE_OR_FAIL (simp_goal_ctac i), CTac.all_ctac)

fun sledgehammer_ctac i (ctxt,thm) =
  case (Hipster_Sledgehammer_Tactics.sledgehammer_get_tac ctxt []
                                        Sledgehammer_Fact.no_fact_override [] i thm) of
  SOME (meth_tac, (meth, facts)) =>
    let
    val hipster_meth = Induction_Data.Sledgehammer_Meth meth
  in
    Seq.map
    (fn nwthm => (Coinduction_Data.add_subgoal_tac_ctxt
                   (i, (hipster_meth,facts)) ctxt, nwthm))
       (meth_tac i thm)
  end
 | NONE => Seq.single (ctxt, thm) (* Do nothing - Sledgehammer failed. *)

val simp_or_sledgehammer_ctac =
  CTac.CTHEN_MAYBE' (simp_no_goal_ctac, sledgehammer_ctac)

fun coinduct_and_sledgehammer_ctac rule =
  CTac.SOLVE_OR_FAIL
    (CTac.CTHEN
      (Seq.DETERM (coinduct_allfree_arbitrary_ctac rule),
       CTac.ALLGOALS simp_or_sledgehammer_ctac))

fun coinduct_upto_and_sledgehammer_ctac rule =
  CTac.SOLVE_OR_FAIL
    (CTac.CTHEN
      (Seq.DETERM (coinduct_upto_allfree_arbitrary_ctac rule),
       CTac.ALLGOALS simp_or_sledgehammer_ctac))

fun thy_expl_sledge_or_coind_ctac  (ctxt0, thm) =
   let
    val ctxt = Coinduction_Data.reset_coind_proof_data_ctxt ctxt0
     in
      CTac.CORELSE
                (CTac.SOLVE_OR_FAIL (CTac.ALLGOALS sledgehammer_ctac),
                 (CTac.CORELSE
                  (CTac.SOLVE_OR_FAIL (coinduct_upto_and_sledgehammer_ctac NONE),
                   coinduct_and_sledgehammer_ctac NONE)))
        (ctxt,thm)
      end

fun thy_expl_coind_ctac (ctxt0, thm) =
   let
    val ctxt = Coinduction_Data.reset_coind_proof_data_ctxt ctxt0
    in
       coinduct_and_sledgehammer_ctac NONE (ctxt,thm)
    end;
end
