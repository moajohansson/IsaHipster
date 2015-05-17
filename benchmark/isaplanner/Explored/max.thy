theory max
imports Main
begin

lemma lemma_a [thy_expl]: "max2 x x = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_aa [thy_expl]: "max2 x Z = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ab [thy_expl]: "max2 x (max2 x y) = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ac [thy_expl]: "max2 x (max2 y x) = max2 y x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ad [thy_expl]: "max2 (max2 x y) x = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ae [thy_expl]: "max2 (S x) y = max2 y (S x)"
by (hipster_induct_schemes max2.simps)

lemma lemma_af [thy_expl]: "max2 x y = max2 y x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ag [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma lemma_a [thy_expl]: ""
by (hipster_induct_schemes max2.simps)

lemma triv_a [thy_expl]: "max2 (max2 x y) y = max2 x y"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ab [thy_expl]: "max2 (S x) (max2 y z) = max2 (max2 y z) (S x)"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ac [thy_expl]: "max2 (max2 x y) Z = max2 x y"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ad [thy_expl]: "max2 (max2 x y) (max2 x y) = max2 x y"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ae [thy_expl]: "max2 (S x) (S x) = S x"
by (hipster_induct_simp_metis max2.simps)

lemma triv_af [thy_expl]: "max2 (S Z) x = max2 x (S Z)"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ag [thy_expl]: "max2 (S Z) (max2 x y) = max2 (max2 x y) (S Z)"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ah [thy_expl]: "max2 (S Z) (S Z) = S Z"
by (hipster_induct_simp_metis max2.simps)

lemma triv_ai [thy_expl]: "max2 (max2 x y) z = max2 z (max2 x y)"
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)

lemma triv_a [thy_expl]: ""
by (hipster_induct_simp_metis max2.simps)


(* FAILED
max2 x (max2 y z) = max2 y (max2 x z)
max2 x (max2 y z) = max2 y (max2 z x)
max2 (max2 x y) z = max2 x (max2 y z)
max2 (max2 x y) z = max2 x (max2 z y)
max2 x (S x) = S x
max2 (S x) x = S x
max2 (max2 x y) (max2 x z) = max2 x (max2 y z)
max2 (max2 x y) (max2 y z) = max2 x (max2 y z)
max2 (max2 x y) (max2 x z) = max2 x (max2 z y)
max2 (max2 x y) (max2 z y) = max2 x (max2 z y)
max2 (max2 x y) (max2 z x) = max2 z (max2 x y)
max2 (max2 x y) (max2 z y) = max2 z (max2 x y)
max2 (max2 x y) (S x) = max2 y (S x)
max2 (max2 x y) (S y) = max2 x (S y)
max2 (S x) (max2 x y) = max2 y (S x)
max2 (S x) (max2 y x) = max2 y (S x)
max2 (S x) (S y) = S (max2 y x)
max2 (S x) (S Z) = S x
max2 (S Z) (S x) = S x
*)











end
