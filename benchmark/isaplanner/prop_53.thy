theory prop_53
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  (*hipster le insort sort equal2 count *)

lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster le*)
lemma lemma_ac [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_af [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes insort.simps)

lemma lemma_ag [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes insort.simps)

lemma lemma_ah [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes insort.simps)

lemma lemma_ai [thy_expl]: "insort Z (sort x2) = sort (insort Z x2)"
by (hipster_induct_schemes  sort.simps)
(*
hipster_cond le insort\<exclamdown>d


hipster_cond equal2 count sort

hipster insort sort count


  theorem x0 :
    "(count n xs) = (count n (sort xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
