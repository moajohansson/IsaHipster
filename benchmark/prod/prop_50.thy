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
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes count.simps equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes count.simps equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes count.simps equal2.simps)

lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps count.simps)

lemma lemma_ad [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_af [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

(*hipster_cond le*)
lemma lemma_ag [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ah [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ai [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

hipster_cond le equal2 insert2 isort count
lemma lemma_aj [thy_expl]: "count x26 (insert2 x26 y26) = S (count x26 y26)"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma lemma_ak [thy_expl]: "insert2 Z (insert2 x26 y26) = insert2 x26 (insert2 Z y26)"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma lemma_al [thy_expl]: "count (S x26) (insert2 x26 y26) = count (S x26) y26"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma lemma_am [thy_expl]: "insert2 Z (isort x3) = isort (insert2 Z x3)"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma lemma_an [thy_expl]: "count (S x4) (insert2 Z y4) = count (S x4) y4"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma lemma_ao [thy_expl]: "le y26 x26 \<Longrightarrow> count (S x26) (insert2 y26 z26) = count (S x26) z26"
by (hipster_induct_schemes le.simps equal2.simps insert2.simps isort.simps count.simps)

lemma unknown [thy_expl]: "insert2 x (insert2 y z) = insert2 y (insert2 x z)"
oops

lemma unknown [thy_expl]: "count x (isort y) = count x y"
oops

lemma unknown [thy_expl]: "isort (insert2 x y) = insert2 x (isort y)"
oops

lemma unknown [thy_expl]: "isort (isort x) = isort x"
oops

lemma unknown [thy_expl]: "count (count x y) (isort z) = count (count x y) z"
oops

lemma unknown [thy_expl]: "count (count x y) (isort y) = count (count x y) y"
oops

lemma unknown [thy_expl]: "count (S x) (isort y) = count (S x) y"
oops

lemma unknown [thy_expl]: "count Z (isort x) = count Z x"
oops

lemma unknown [thy_expl]: "count (count Z x) (isort y) = count (count Z x) y"
oops

lemma unknown [thy_expl]: "count (count Z x) (isort x) = count (count Z x) x"
oops

lemma unknown [thy_expl]: "count (S Z) (isort x) = count (S Z) x"
oops

datatype NL = NN | NC Nat NL

  fun ins2 :: "Nat => NL => NL" where
  "ins2 x (NN) = NC x (NN)"
  | "ins2 x (NC z xs) =
       (if le x z then NC x (NC z xs) else NC z (ins2 x xs))"
  fun cou :: "Nat => NL => Nat" where
  "cou x (NN) = Z"
  | "cou x (NC z xs) =
       (if equal2 x z then S (cou x xs) else cou x xs)"
hipster cou ins2 le equal2
lemma lemma_ap [thy_expl]: "NC Z x3 = ins2 Z x3"
by (hipster_induct_schemes cou.simps ins2.simps le.simps equal2.simps)

lemma lemma_aq [thy_expl]: "count x (Cons2 y z) = count x (insert2 y z)"
by (hipster_induct_schemes count.simps insert2.simps le.simps equal2.simps)

lemma unknown [thy_expl]: "ins2 x (ins2 y z) = ins2 y (ins2 x z)"
oops

lemma unknown [thy_expl]: "ins2 x (ins2 y NN) = ins2 y (ins2 x NN)"
oops
(*hipster count insert2 isort le*)

  theorem x0 :
    "(count x (isort y)) = (count x y)"
    by (hipster_induct_schemes count.simps isort.simps insert2.simps le.simps equal2.simps)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
