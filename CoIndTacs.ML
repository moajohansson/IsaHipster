(*  Author:     Sólrún Halla Einarsdóttir, Chalmers University of Technology
    Hipster coinduction tactics *)

signature COIND_TACS =
sig
  (* Coinduction with specified vars set to arbitrary *)
  val coinduct_with_arbitrary_tac: Proof.context -> term list  -> tactic

  (* Coinduction with all free variables set to arbitrary *)
  val coinduct_allfree_arbitrary_tac: Proof.context -> tactic

  (* Coinduction with all free vars set to arbitrary,
     then try to use sledgehammer to prove remaining subgoals *)
  val coinduct_and_sledgehammer: Proof.context -> tactic

end


structure Coind_Tacs : COIND_TACS =
struct
  fun coinduct_with_arbitrary_tac ctxt vars goalthm =
    let val nw_thms = HEADGOAL(Coinduction.coinduction_tac ctxt vars NONE []) goalthm
    in
      nw_thms
  end;
  fun coinduct_allfree_arbitrary_tac ctxt goalthm =
    let val t = Thm.concl_of goalthm
        val fvs = Hipster_Utils.add_term_frees(t, [])
        val nw_thms = coinduct_with_arbitrary_tac ctxt fvs goalthm
    in
      nw_thms
  end;
  fun coinduct_and_sledgehammer ctxt =
    DEPTH_SOLVE (
      (Seq.DETERM ((coinduct_allfree_arbitrary_tac ctxt) THEN
                    (Ind_Tacs.simp_or_sledgehammer_tac ctxt))))
end

signature EXPL_TACS =
sig
  val routine_tac : Proof.context -> tactic
  val routine_tac_str : string
  val hard_tac : Proof.context ->  tactic
  val final_tactic_str : Proof.context -> string
end

structure Coinduct_T : EXPL_TACS =
struct
  fun routine_tac ctxt =
    let val lemmas = (ThyExpl_Data.proved_of_ctxt ctxt) @ (Hipster_Rules.get ctxt)
    in
      SOLVE (Ind_Tacs.prove_by_simp ctxt lemmas)
    end;

  val routine_tac_str = "by (tactic {*Simp_Tacs.routine_tac @{context}*})";
  fun hard_tac ctxt = Coind_Tacs.coinduct_and_sledgehammer ctxt
  fun final_tactic_str _ = "by hipster_coinduct"
end
