theory prop_61
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
  | "lastOfTwo x (Cons2 z x2) = last (Cons2 z x2)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster last lastOfTwo append *)

(*hipster lastOfTwo*)
lemma lemma_a [thy_expl]: "prop_61.last x2 = lastOfTwo x2 x2"
by (hipster_induct_schemes prop_61.lastOfTwo.simps)
hipster append last
lemma lemma_aa [thy_expl]: "prop_61.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_61.append.simps prop_61.last.simps)

lemma lemma_ab [thy_expl]: "prop_61.append (prop_61.append x2 y2) z2 =
prop_61.append x2 (prop_61.append y2 z2)"
by (hipster_induct_schemes prop_61.append.simps prop_61.last.simps)
  theorem x0 :
    "(last (append xs ys)) = (lastOfTwo xs ys)"
    apply(hipster_induct_schemes)
    apply(induction xs ys rule:lastOfTwo.induct)
    apply(simp_all)
    apply(metis lemma_aa lastOfTwo.simps)

    (*apply(hipster_induct_schemes lastOfTwo.simps append.simps)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
