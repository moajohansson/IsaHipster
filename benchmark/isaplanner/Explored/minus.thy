theory minus
imports Main

begin

lemma lemma_a [thy_expl]: "prop_07.minus x2 x2 = Z"
by (hipster_induct_schemes prop_07.minus.simps)

lemma lemma_aa [thy_expl]: "prop_07.minus x3 Z = x3"
by (hipster_induct_schemes prop_07.minus.simps)

lemma lemma_ab [thy_expl]: "prop_07.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_07.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_07.minus (prop_07.minus x3 y3) (prop_07.minus y3 x3) =
prop_07.minus x3 y3"
by (hipster_induct_schemes prop_07.minus.simps)

lemma lemma_ae [thy_expl]: "prop_07.minus (prop_07.minus x3 y3) (S Z) = prop_07.minus x3 (S y3)"
by (hipster_induct_schemes prop_07.minus.simps)

lemma lemma_af [thy_expl]: "prop_07.minus (prop_07.minus x4 y4) x4 = Z"
by (hipster_induct_schemes prop_07.minus.simps)

end