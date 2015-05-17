theory prop_02
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster length append *)

lemma lemma_a [thy_expl]: "prop_02.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_02.length.simps prop_02.append.simps)

lemma lemma_aa [thy_expl]: "prop_02.append (prop_02.append x2 y2) z2 =
prop_02.append x2 (prop_02.append y2 z2)"
by (hipster_induct_schemes prop_02.length.simps prop_02.append.simps)

lemma unknown [thy_expl]: "prop_02.length (prop_02.append x y) = prop_02.length (prop_02.append y x)"
oops

lemma ax: "prop_02.length (prop_02.append (Cons2 ya xs) y) = S (prop_02.length (prop_02.append xs y))"
by (metis length.simps(2) prop_02.append.simps(2))

lemma ax2: "prop_02.length (prop_02.append y (Cons2 ya xs)) = S (prop_02.length (prop_02.append y xs))"
by(hipster_induct_schemes)

  theorem x0 :
    "(length (append x y)) = (length (append y x))"
    by(hipster_induct_schemes ax2)
    (*apply(hipster_induct_schemes length.simps append.simps thy_expl list.exhaust)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
