theory prop_46
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
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  (*hipster le insert2 equal2 elem *)

(*hipster equal2*)
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster_cond equal2*)

lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps)

hipster le equal2
lemma lemma_ad [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ae [thy_expl]: "equal2 x2 Z = le x2 Z"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_af [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ag [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps equal2.simps)

(*hipster_cond le
hipster_cond equal2 le
hipster_cond equal2 elem
hipster_cond le elem
hipster_cond elem equal2
hipster_cond elem le
hipster insert2 elem equal2 le
hipster_cond elem equal2*)

  theorem x0 :
    "(x = y) ==> (elem x (insert2 y z))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
