theory prop_38
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
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster equal2 count append *)
lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes prop_38.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_38.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_38.equal2.simps)

  theorem x0 :
    "(count n (append xs (Cons2 n (Nil2)))) = (S (count n xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
