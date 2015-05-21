theory max
imports Main
        "../data/Nat"
        "../../IsaHipster"

begin

fun max2 :: "Nat => Nat => Nat" where
  "max2 Z Z = Z"
| "max2 (Z) (S y) = y"
| "max2 (S z) (Z) = S z"
| "max2 (S z) (S x2) = S (max2 z x2)"

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

end

