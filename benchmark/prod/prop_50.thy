theory prop_50
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if equal2 x z then S (count x xs) else count x xs)"
  (*hipster le insert2 isort equal2 count *)
hipster count equal2
lemma lemma_a [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 Z x2 = equal2 x2 Z"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

lemma lemma_ac [thy_expl]: "equal2 (S x2) x2 = False"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

lemma lemma_ad [thy_expl]: "equal2 (S Z) x2 = equal2 x2 (S Z)"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

lemma lemma_ae [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes prop_50.count.simps prop_50.equal2.simps)

hipster count insert2 isort le

  theorem x0 :
    "(count x (isort y)) = (count x y)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
