theory drop
imports Main
begin
lemma lemma_a [thy_expl]: "prop_56.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_56.drop.simps)

lemma lemma_aa [thy_expl]: "prop_56.drop (S Z) (prop_56.drop x3 y3) = prop_56.drop (S x3) y3"
by (hipster_induct_schemes prop_56.drop.simps)

lemma unknown [thy_expl]: "prop_56.drop x (prop_56.drop y z) = prop_56.drop y (prop_56.drop x z)"
oops

lemma unknown [thy_expl]: "prop_56.drop (S x) (prop_56.drop y z) =
prop_56.drop (S y) (prop_56.drop x z)"
oops

end
