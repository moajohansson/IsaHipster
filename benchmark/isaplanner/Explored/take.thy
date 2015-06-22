theory take
imports Main

begin

lemma lemma_ai [thy_expl]: "prop_57.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_aj [thy_expl]: "prop_57.take x3 (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_ak [thy_expl]: "prop_57.take (S x3) (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)

lemma unknown [thy_expl]: "prop_57.take x (prop_57.take y z) = prop_57.take y (prop_57.take x z)"
oops

end
