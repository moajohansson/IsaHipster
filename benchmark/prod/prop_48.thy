theory prop_48
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "Nat list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
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
  (*hipster length le insert2 isort *)

(*
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)*)

(*hipster length le insert2 isort*)
lemma lemma_af [thy_expl]: "S (length x5) = length (insert2 y5 x5)"
by (hipster_induct_schemes length.simps  insert2.simps isort.simps)

lemma lemma_ag [thy_expl]: "length (isort x17) = length x17"
by (hipster_induct_schemes )
(*
lemma lemma_ah [thy_expl]: "insert2 Z (insert2 x18 y18) = insert2 x18 (insert2 Z y18)"
by (hipster_induct_schemes length.simps le.simps insert2.simps isort.simps)

lemma lemma_ai [thy_expl]: "insert2 Z (isort x3) = isort (insert2 Z x3)"
by (hipster_induct_schemes length.simps le.simps insert2.simps isort.simps)*)

  theorem x0 :
    "(length (isort x)) = (length x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
