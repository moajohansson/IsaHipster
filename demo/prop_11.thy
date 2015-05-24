theory prop_11
imports Main
        "../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"

  fun append :: "'a list => 'a list => 'a list" where
    "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"

  fun rev :: "'a list => 'a list" where
    "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"

declare [[thy_interesting = true]]

(*hipster append rev*)
lemma lemma_a [thy_expl]: "prop_11.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_aa [thy_expl]: "prop_11.append (prop_11.append x2 y2) z2 =
prop_11.append x2 (prop_11.append y2 z2)"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_ab [thy_expl]: "prop_11.append (prop_11.rev x5) (prop_11.rev y5) =
prop_11.rev (prop_11.append y5 x5)"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_ac [thy_expl]: "prop_11.rev (prop_11.rev x5) = x5"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)



  theorem revAppend :
    "(rev (append (rev x) (rev y))) = (append y x)"
    by (hipster_induct_schemes rev.simps append.simps)

ML_val {*
  (*proof body with digest*)
  val body = Proofterm.strip_thm (Thm.proof_body_of @{thm revAppend});
  (*proof term only*)
  val prf = Proofterm.proof_of body;
  Pretty.writeln (Proof_Syntax.pretty_proof @{context} prf);
  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn (name, _, _) => insert (op =) name) [body] [];
  map 
*}

thm prop_11.list.rec
find_theorems


ML {*
  Datatype.distinct_lemma ;
  val _ = Pretty.writeln (Proof_Syntax.pretty_proof @{context} (Thm.proof_of @{thm revAppend}))
*}

help find
find_consts
find_theorems
find_unused_assms
print_options

thm_deps lemma_a
thm append_sumC_def
thm append.elims
thm append.simps

(*
lemma lemma_a [thy_expl]: "prop_11.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_aa [thy_expl]: "prop_11.append (prop_11.append x2 y2) z2 =
prop_11.append x2 (prop_11.append y2 z2)"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_ab [thy_expl]: "prop_11.append (prop_11.rev x5) (prop_11.rev y5) =
prop_11.rev (prop_11.append y5 x5)"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)

lemma lemma_ac [thy_expl]: "prop_11.rev (prop_11.rev x5) = x5"
by (hipster_induct_schemes prop_11.append.simps prop_11.rev.simps)
*)
  theorem x0 :
    "(rev (append (rev x) (rev y))) = (append y x)"
    by hipster_induct_schemes
    






    (*by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
