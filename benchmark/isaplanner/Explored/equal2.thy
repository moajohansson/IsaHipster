theory equal2
imports Main

begin

lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes prop_05.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_05.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_05.equal2.simps)

end