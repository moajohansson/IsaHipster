theory min
imports Main
begin

lemma lemma_a [thy_expl]: "min2 x x = x"
by (hipster_induct_schemes min2.simps)

lemma lemma_aa [thy_expl]: "min2 x Z = x"
by (hipster_induct_schemes min2.simps)

lemma lemma_ab [thy_expl]: "min2 x (min2 x y) = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ac [thy_expl]: "min2 x (min2 y x) = min2 y x"
by (hipster_induct_schemes min2.simps)

lemma lemma_ad [thy_expl]: "min2 (min2 x y) x = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ae [thy_expl]: "min2 (S x) y = min2 y (S x)"
by (hipster_induct_schemes min2.simps)

lemma lemma_af [thy_expl]: "min2 x y = min2 y x"
by (hipster_induct_schemes min2.simps)

lemma lemma_ag [thy_expl]: ""
by (hipster_induct_schemes min2.simps)

lemma triv_a [thy_expl]: "min2 (min2 x y) y = min2 x y"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ab [thy_expl]: "min2 (S x) (min2 y z) = min2 (min2 y z) (S x)"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ac [thy_expl]: "min2 (min2 x y) Z = min2 x y"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ad [thy_expl]: "min2 (min2 x y) (min2 x y) = min2 x y"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ae [thy_expl]: "min2 (S x) (S x) = S x"
by (hipster_induct_simp_metis min2.simps)

lemma triv_af [thy_expl]: "min2 (S Z) x = min2 x (S Z)"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ag [thy_expl]: "min2 (S Z) (min2 x y) = min2 (min2 x y) (S Z)"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ah [thy_expl]: "min2 (S Z) (S Z) = S Z"
by (hipster_induct_simp_metis min2.simps)

lemma triv_ai [thy_expl]: "min2 (min2 x y) z = min2 z (min2 x y)"
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis min2.simps)


(* FAILED
min2 x (min2 y z) = min2 y (min2 x z)
min2 x (min2 y z) = min2 y (min2 z x)
min2 (min2 x y) z = min2 x (min2 y z)
min2 (min2 x y) z = min2 x (min2 z y)
min2 x (S x) = S x
min2 (S x) x = S x
min2 (min2 x y) (min2 x z) = min2 x (min2 y z)
min2 (min2 x y) (min2 y z) = min2 x (min2 y z)
min2 (min2 x y) (min2 x z) = min2 x (min2 z y)
min2 (min2 x y) (min2 z y) = min2 x (min2 z y)
min2 (min2 x y) (min2 z x) = min2 z (min2 x y)
min2 (min2 x y) (min2 z y) = min2 z (min2 x y)
min2 (min2 x y) (S x) = min2 y (S x)
min2 (min2 x y) (S y) = min2 x (S y)
min2 (S x) (min2 x y) = min2 y (S x)
min2 (S x) (min2 y x) = min2 y (S x)
min2 (S x) (S y) = S (min2 y x)
min2 (S x) (S Z) = S x
min2 (S Z) (S x) = S x
*)











end
