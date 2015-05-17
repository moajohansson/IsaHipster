theory prop_60
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun null2 :: "'a list => bool" where
  "null2 (Nil2) = True"
  | "null2 (Cons2 y z) = False"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster null last append *)
(*hipster last null2 append*)
lemma lemma_a [thy_expl]: "prop_60.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_60.last.simps prop_60.null2.simps prop_60.append.simps)

lemma lemma_aa [thy_expl]: "prop_60.append (prop_60.append x2 y2) z2 =
prop_60.append x2 (prop_60.append y2 z2)"
by (hipster_induct_schemes prop_60.last.simps prop_60.null2.simps prop_60.append.simps)

lemma lemma_ab [thy_expl]: "null2 (prop_60.append x2 x2) = null2 x2"
by (hipster_induct_schemes prop_60.last.simps prop_60.null2.simps prop_60.append.simps)

lemma unknown [thy_expl]: "null2 (prop_60.append x y) = null2 (prop_60.append y x)"
oops

  theorem x0 :
    "(~ (null2 ys)) ==> ((last (append xs ys)) = (last ys))"

    by (hipster_induct_schemes last.simps null.simps append.simps list.exhaust)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
