theory equal
imports Main
        "../data/Nat"
        "../../IsaHipster"
begin

fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

lemma lemma_a [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes  equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 Z x2 = equal2 x2 Z"
by (hipster_induct_schemes  equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes  equal2.simps)

lemma lemma_ac [thy_expl]: "equal2 (S x2) x2 = False"
by (hipster_induct_schemes  equal2.simps)

lemma lemma_ad [thy_expl]: "equal2 (S Z) x2 = equal2 x2 (S Z)"
by (hipster_induct_schemes  equal2.simps)

lemma lemma_ae [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes  equal2.simps)

end

