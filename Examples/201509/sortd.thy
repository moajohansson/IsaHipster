theory sortd

imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

  datatype 'a list = Nil | Cons "'a" "'a list"
  datatype Nat = Z | S "Nat"

  fun le :: "Nat => Nat => bool" where
    "le Z y = True"
  | "le (S z) Z = False"
  | "le (S z) (S x2) = le z x2"

  fun sorted :: "Nat list => bool" where
  "sorted Nil = True"
  | "sorted (Cons y (Nil)) = True"
  | "sorted (Cons y (Cons y2 xs)) =
       (if le y y2 then sorted (Cons y2 xs) else False)"

  fun insert :: "Nat => Nat list => Nat list" where
  "insert x Nil = Cons x (Nil)"
  | "insert x (Cons z xs) =
       (if le x z then Cons x (Cons z xs) else Cons z (insert x xs))"

  fun isort :: "Nat list => Nat list" where
  "isort Nil = Nil"
  | "isort (Cons y xs) = insert y (isort xs)"


hipster le
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps Nat.exhaust)

hipster_cond le
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)


(*hipster_cond sorted isort insert le *)
lemma lemma_af [thy_expl]: "insert Z (insert x20 y20) = insert x20 (insert Z y20)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_ag [thy_expl]: "sorted (insert Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_ah [thy_expl]: "insert Z (isort x3) = isort (insert Z x3)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

  fun notle :: "Nat => Nat => bool" where
    "notle x y = (\<not> le x y)"

hipster_cond notle
hipster notle le
lemma lemma_ai [thy_expl]: "notle (S x2) y2 = le y2 x2"
by (hipster_induct_schemes sortd.notle.simps sortd.Nat.exhaust)

lemma lemma_aj [thy_expl]: "notle x2 y2 \<Longrightarrow> notle x2 Z = True"
by (hipster_induct_schemes sortd.notle.simps sortd.Nat.exhaust)

lemma lemma_ [thy_expl]: "le (S x11) y11 = (\<not> le y11 x11)"
by (hipster_induct_schemes sortd.notle.simps sortd.le.simps sortd.Nat.exhaust)

(* include negation: discovered if declared separately *)
lemma nole []: "\<not> le r s \<Longrightarrow> le s r"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*hipster_cond sorted isort insert le*)
lemma lemma_ai [thy_expl]: "insert x32 (insert y32 z32) = insert y32 (insert x32 z32)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_aj [thy_expl]: "isort (insert x19 y19) = insert x19 (isort y19)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_ak [thy_expl]: "isort (isort x19) = isort x19"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

setup {* Hip_Tac_Ops.set_full_types @{context} true *}
setup {* Hip_Tac_Ops.set_metis_to @{context} 700 *}

lemma lemma_al [thy_expl]: "sorted x \<Longrightarrow> isort x = x"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

setup {* Hip_Tac_Ops.set_metis_to @{context} 1000 *}

lemma lemma_am [thy_expl]: "sorted y \<Longrightarrow> sorted (insert x y) = True"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps)

lemma lemma_an [thy_expl]: "sorted (isort x) = True"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps)

lemma lemma_ao [thy_expl]: "sorted y \<Longrightarrow> isort (insert x y) = insert x y"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps)
(*
lemma lemma_ap [thy_expl]: "sorted (insert x y) = sorted y"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps Nat.exhaust)*)


  theorem x0 :
    "sorted (isort x)"
    by hipster_induct_schemes

(*    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *}) *)


end
