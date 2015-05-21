theory min
imports Main
        "../data/Nat"
        "../../IsaHipster"

begin

fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
| "min2 (S z) (Z) = Z"
| "min2 (S z) (S y1) = S (min2 z y1)"

lemma lemma_a [thy_expl]: "min2 x x = x"
by (hipster_induct_schemes min2.simps)

lemma lemma_aa [thy_expl]: "min2 x Z = Z"
by (hipster_induct_schemes min2.simps)

lemma lemma_ab [thy_expl]: "min2 x (min2 x y) = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ac [thy_expl]: "min2 x (min2 y x) = min2 y x"
by (hipster_induct_schemes min2.simps)

lemma lemma_ad [thy_expl]: "min2 (min2 x y) x = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ae []: "min2 (S x) y = min2 y (S x)"
by (hipster_induct_schemes min2.simps)

lemma lemma_af [thy_expl]: "min2 x y = min2 y x"
by (hipster_induct_schemes min2.simps)

end

