theory prop_28
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster equal2 elem append *)
lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes prop_28.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_28.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_28.equal2.simps)

  theorem x0 :
    "elem x (append xs (Cons2 x (Nil2)))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
