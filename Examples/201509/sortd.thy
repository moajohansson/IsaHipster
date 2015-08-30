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


  fun notle :: "Nat => Nat => bool" where
    "notle x y = (\<not> le x y)"

hipster_cond notle le
lemma lemma_ac [thy_expl]: "\<not> le (S x12) y12 = le y12 x12"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ad [thy_expl]: "\<not> le y11 x11 \<Longrightarrow> \<not> le x11 y11 = False"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ae [thy_expl]: "\<not> le z11 x11 \<and> \<not> le y11 z11 \<Longrightarrow> le x11 y11 = True"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_af [thy_expl]: "\<not> le z11 y11 \<and> \<not> le x11 z11 \<Longrightarrow> le x11 (S y11) = False"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ag [thy_expl]: "\<not> le z11 y11 \<and> \<not> le x11 z11 \<Longrightarrow>
\<not> le (S x11) (S y11) = True"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ah [thy_expl]: "\<not> le z11 x11 \<and> \<not> le y11 z11 \<Longrightarrow>
le (S x11) (S y11) = True"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ai [thy_expl]: "\<not> le z11 y11 \<and> \<not> le x11 z11 \<Longrightarrow>
le (S x11) (S y11) = False"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_aj [thy_expl]: "\<not> le z11 x11 \<and> \<not> le y11 z11 \<Longrightarrow> \<not> le x11 y11 = False"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_ak [thy_expl]: "\<not> le z11 y11 \<and> \<not> le x11 z11 \<Longrightarrow> \<not> le x11 y11 = True"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

lemma lemma_al [thy_expl]: "\<not> le z11 y11 \<and> \<not> le x11 z11 \<Longrightarrow> le x11 y11 = False"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

hipster_cond le
lemma lemma_am [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_an [thy_expl]: "le y9 x9 \<and> le x9 y9 \<Longrightarrow> x9 = y9"
by (hipster_induct_schemes le.simps Nat.exhaust)
(*
lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x (S y) = True"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> le (S x) y = False"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le (S x) (S y) = True"
oops
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)
*)
lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)


hipster_cond sorted isort insert le
lemma lemma_ao [thy_expl]: "insert Z (insert x22 y22) =
insert x22 (insert Z y22)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_ap [thy_expl]: "sorted (insert Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_aq [thy_expl]: "insert Z (isort x3) = isort (insert Z x3)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_ar [thy_expl]: "insert x (insert y z) = insert y (insert x z)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma lemma_as [thy_expl]: "isort (insert x y) = insert x (isort y)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma unknown []: "sorted (insert x y) = sorted y"
oops

lemma lemma_at [thy_expl]: "isort (isort x) = isort x"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps list.exhaust Nat.exhaust)

lemma unknown []: "sorted (isort x) = True"
oops

lemma unknown [thy_expl]: "sorted x \<Longrightarrow> isort x = x"
oops

lemma unknown [thy_expl]: "sorted y \<Longrightarrow> isort (insert x y) = insert x y"
oops

lemma unknown [thy_expl]: "sorted y \<Longrightarrow> sorted (insert x y) = True"
oops

lemma unknown [thy_expl]: "sorted x \<Longrightarrow> isort (insert Z x) = insert Z x"
oops
lemma lemma_af [thy_expl]: "insert Z (insert x20 y20) = insert x20 (insert Z y20)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_ag [thy_expl]: "sorted (insert Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)

lemma lemma_ah [thy_expl]: "insert Z (isort x3) = isort (insert Z x3)"
by (hipster_induct_schemes sorted.simps isort.simps insert.simps le.simps)
*)

(*hipster_cond notle
hipster notle le
lemma lemma_adi [thy_expl]: "\<not> le (S x2) y2 = le y2 x2"
by (hipster_induct_schemes notle.simps Nat.exhaust)

lemma lemma_adj [thy_expl]: "\<not> le x2 y2 \<Longrightarrow> \<not> le x2 Z = True"
by (hipster_induct_schemes notle.simps Nat.exhaust)

lemma lemma_ [thy_expl]: "le (S x11) y11 = (\<not> le y11 x11)"
by (hipster_induct_schemes notle.simps le.simps Nat.exhaust)

(* include negation: discovered if declared separately *)
lemma nole []: "\<not> le r s \<Longrightarrow> le s r"
by (hipster_induct_schemes le.simps Nat.exhaust)
*)
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
