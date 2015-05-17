theory prop_19
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster minus len drop *)
(*hipster minus*)
lemma lemma_a [thy_expl]: "prop_19.minus x2 x2 = Z"
by (hipster_induct_schemes prop_19.minus.simps)

lemma lemma_aa [thy_expl]: "prop_19.minus x3 Z = x3"
by (hipster_induct_schemes prop_19.minus.simps)

lemma lemma_ab [thy_expl]: "prop_19.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_19.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_19.minus (prop_19.minus x3 y3) (prop_19.minus y3 x3) =
prop_19.minus x3 y3"
by (hipster_induct_schemes prop_19.minus.simps)

lemma lemma_ae [thy_expl]: "prop_19.minus (prop_19.minus x3 y3) (S Z) = prop_19.minus x3 (S y3)"
by (hipster_induct_schemes prop_19.minus.simps)

lemma lemma_af [thy_expl]: "prop_19.minus (prop_19.minus x4 y4) x4 = Z"
by (hipster_induct_schemes prop_19.minus.simps)

lemma woop [thy_expl]: "prop_19.minus (prop_19.minus x y) z = prop_19.minus (prop_19.minus x z) y"
apply(induction x y rule: minus.induct)
apply (simp_all add: lemma_af lemma_ae lemma_ad lemma_ac lemma_ab lemma_aa)
proof -
  fix za :: Nat and x2 :: Nat
  obtain esk4\<^sub>1 :: "Nat \<Rightarrow> Nat" where "\<And>x1. S (prop_19.minus x1 (S Z)) = x1 \<or> Z = x1" by (metis (no_types) Nat.exhaust lemma_aa minus.simps(3))
  hence "\<And>x1 x2. prop_19.minus (S x1) x2 = S (prop_19.minus x1 x2) \<or> prop_19.minus (S x1) x2 = Z" by (metis (no_types) lemma_ae minus.simps(3))
  thus "prop_19.minus (prop_19.minus za z) x2 = prop_19.minus (prop_19.minus (S za) z) (S x2)" by (metis (no_types) lemma_ae minus.simps(1) minus.simps(3))
qed

lemma unknown [thy_expl]: "prop_19.minus x (prop_19.minus x y) = prop_19.minus y (prop_19.minus y x)"
oops

lemma unknown [thy_expl]: "prop_19.minus (prop_19.minus x y) (prop_19.minus z y) =
prop_19.minus (prop_19.minus x z) (prop_19.minus y z)"
oops

lemma unknown [thy_expl]: "prop_19.minus (prop_19.minus x y) (S z) =
prop_19.minus (prop_19.minus x z) (S y)"
oops

lemma unknown [thy_expl]: "prop_19.minus (prop_19.minus x y) (prop_19.minus z y) =
prop_19.minus (prop_19.minus x y) z"
oops

lemma unknown [thy_expl]: "prop_19.minus (prop_19.minus x y) (prop_19.minus z y) =
prop_19.minus (prop_19.minus x z) y"
oops

lemma unknown [thy_expl]: "prop_19.minus (prop_19.minus x y) (prop_19.minus x z) =
prop_19.minus (prop_19.minus z y) (prop_19.minus z x)"
oops

lemma unknown [thy_expl]: "prop_19.minus (S x) (prop_19.minus x y) =
prop_19.minus (S y) (prop_19.minus y x)"
oops
  theorem x0 :
    "(len (drop n xs)) = (minus (len xs) n)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
