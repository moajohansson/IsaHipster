theory prop_14
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
  | "sorted (Cons2 y (Nil2)) = True"
  | "sorted (Cons2 y (Cons2 y2 xs)) =
       (if le y y2 then sorted (Cons2 y2 xs) else False)"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  (*hipster le sorted insert2 isort *)

hipster le
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
by (hipster_induct_schemes le.simps Nat.exhaust)


(*hipster_cond sorted isort insert2 le*)
lemma lemma_af [thy_expl]: "insert2 Z (insert2 x20 y20) = insert2 x20 (insert2 Z y20)"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

lemma lemma_ag [thy_expl]: "sorted (insert2 Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

lemma lemma_ah [thy_expl]: "insert2 Z (isort x3) = isort (insert2 Z x3)"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

(* include negation: discovered if declared separately *)
lemma nole [thy_expl]: "\<not> le r s \<Longrightarrow> le s r"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*hipster_cond sorted isort insert2 le*)
lemma lemma_ai [thy_expl]: "insert2 x32 (insert2 y32 z32) = insert2 y32 (insert2 x32 z32)"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

lemma lemma_aj [thy_expl]: "isort (insert2 x19 y19) = insert2 x19 (isort y19)"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

lemma lemma_ak [thy_expl]: "isort (isort x19) = isort x19"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

setup \<open>Hip_Tac_Ops.set_full_types @{context} true\<close>
setup \<open>Hip_Tac_Ops.set_metis_to @{context} 700\<close>

lemma lemma_al [thy_expl]: "sorted x \<Longrightarrow> isort x = x"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)

setup \<open>Hip_Tac_Ops.set_metis_to @{context} 1000\<close>

lemma lemma_am [thy_expl]: "sorted y \<Longrightarrow> sorted (insert2 x y) = True"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps nole)

lemma lemma_an [thy_expl]: "sorted (isort x) = True"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps)

lemma lemma_ao [thy_expl]: "sorted y \<Longrightarrow> isort (insert2 x y) = insert2 x y"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps)
(*
lemma lemma_ap [thy_expl]: "sorted (insert2 x y) = sorted y"
by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps Nat.exhaust)*)


  theorem x0 :
    "sorted (isort x)"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
