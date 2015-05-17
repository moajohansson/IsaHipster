theory prop_66
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun filter2 :: "('a => bool) => 'a list => 'a list" where
  "filter2 x (Nil2) = Nil2"
  | "filter2 x (Cons2 z xs) =
       (if x z then Cons2 z (filter2 x xs) else filter2 x xs)"
  (*hipster len le filter *)
hipster len filter2
lemma lemma_a [thy_expl]: "filter2 x13 (filter2 y13 z13) = filter2 y13 (filter2 x13 z13)"
by (hipster_induct_schemes prop_66.len.simps prop_66.filter2.simps)

lemma lemma_aa [thy_expl]: "filter2 x9 (filter2 x9 y9) = filter2 x9 y9"
by (hipster_induct_schemes prop_66.len.simps prop_66.filter2.simps)

hipster le
lemma lemma_ab [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes prop_66.le.simps)

lemma lemma_ac [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes prop_66.le.simps)

lemma lemma_ad [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes prop_66.le.simps)

  theorem x0 :
    "le (len (filter2 q xs)) (len xs)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
