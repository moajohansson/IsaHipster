theory prop_05
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
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster length append rev *)

lemma lemma_a [thy_expl]: "prop_05.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_05.length.simps prop_05.append.simps)

lemma lemma_aa [thy_expl]: "prop_05.append (prop_05.append x2 y2) z2 =
prop_05.append x2 (prop_05.append y2 z2)"
by (hipster_induct_schemes prop_05.length.simps prop_05.append.simps)

hipster rev append
lemma lemma_ab [thy_expl]: "prop_05.append (prop_05.rev x5) (prop_05.rev y5) =
prop_05.rev (prop_05.append y5 x5)"
by (hipster_induct_schemes prop_05.rev.simps prop_05.append.simps)

lemma lemma_ac [thy_expl]: "prop_05.rev (prop_05.rev x5) = x5"
by (hipster_induct_schemes prop_05.rev.simps prop_05.append.simps)

lemma ax: "prop_05.length (prop_05.append (Cons2 ya xs) y) = S (prop_05.length (prop_05.append xs y))"
by (metis length.simps(2) prop_05.append.simps(2))

lemma ax2[thy_expl]: "prop_05.length (prop_05.append y (Cons2 ya xs)) = S (prop_05.length (prop_05.append y xs))"
by(hipster_induct_schemes)

  theorem x0 :
    "(length (rev x)) = (length x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
