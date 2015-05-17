theory prop_10
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster append rev *)

(*hipster rev*)
lemma lemma_a [thy_expl]: "prop_10.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_10.rev.simps)

lemma lemma_aa [thy_expl]: "prop_10.append (prop_10.append x2 y2) z2 =
prop_10.append x2 (prop_10.append y2 z2)"
by (hipster_induct_schemes prop_10.rev.simps)

lemma lemma_ab [thy_expl]: "prop_10.append (prop_10.rev x5) (prop_10.rev y5) =
prop_10.rev (prop_10.append y5 x5)"
by (hipster_induct_schemes prop_10.rev.simps)

lemma unknown [thy_expl]: "prop_10.rev (prop_10.rev x) = x"
oops

  theorem x0 :
    "(rev (rev x)) = x"
    by(hipster_induct_schemes rev.simps append.simps thy_expl)
    (* by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
