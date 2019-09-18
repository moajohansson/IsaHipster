theory prop_03
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
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
  (*hipster le equal2 count append *)

hipster_cond le equal2
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
apply(induction x2 arbitrary: y2)
apply simp_all
sledgehammer
apply(metis equal2.simps)
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemm_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
apply(induction x2 y2 rule: equal2.induct)

lemma lemma_aa [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ac [thy_expl]: "equal2 x2 Z = le x2 Z"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ad [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ae [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_af [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ag [thy_expl]: "le x14 y14 \<Longrightarrow> equal2 x14 y14 = le y14 x14"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ah [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps equal2.simps)

lemma lemma_ai [thy_expl]: "le x2 y2 \<Longrightarrow> equal2 x2 (S y2) = False"
by (hipster_induct_schemes le.simps equal2.simps)

lemma unknown [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
oops
thm Nat.exhaust
lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> equal2 x y = le x y"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> equal2 x y = le y x"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x (S y) = True"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> equal2 x (S y) = False"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> le (S x) y = False"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> equal2 (S x) y = False"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le (S x) (S y) = True"
oops

lemma unknown [thy_expl]: "le z x \<and> le y z \<Longrightarrow> equal2 (S x) (S y) = le x y"
oops

lemma unknown [thy_expl]: "le z y \<and> le x z \<Longrightarrow> equal2 (S x) (S y) = le y x"
oops

  theorem x0 :
    "le (count n xs) (count n (append xs ys))"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
