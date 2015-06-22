theory minus
imports Main
        "../data/Natu"
        "../../IsaHipster"
begin

fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
| "minus (S z) (Z) = S z"
| "minus (S z) (S x2) = minus z x2"

lemma lemma_a [thy_expl]: "minus x2 x2 = Z"
by (hipster_induct_schemes minus.simps)

lemma lemma_aa [thy_expl]: "minus x3 Z = x3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ab [thy_expl]: "minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "minus (minus x3 y3) (minus y3 x3) = minus x3 y3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ae [thy_expl]: "minus (minus x3 y3) (S Z) = minus x3 (S y3)"
by (hipster_induct_schemes minus.simps)

lemma lemma_af [thy_expl]: "minus (minus x4 y4) x4 = Z"
by (hipster_induct_schemes minus.simps)

end

