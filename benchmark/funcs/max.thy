theory max
imports Main
        "../data/Natu"
        "../../IsaHipster"

begin

fun max2 :: "Nat => Nat => Nat" where
  "max2 Z Z = Z"
| "max2 (Z) (S y) = S y"
| "max2 (S z) (Z) = S z"
| "max2 (S z) (S x2) = S (max2 z x2)"

(*hipster max2*)
hipster max2
lemma lemma_a [thy_expl]: "max2 x2 y2 = max2 y2 x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_aa [thy_expl]: "max2 x2 x2 = x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ab [thy_expl]: "max2 x2 Z = x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ac [thy_expl]: "max2 x1 (max2 x1 y1) = max2 x1 y1"
by (hipster_induct_schemes max2.simps)

lemma lemma_ad [thy_expl]: "max2 x2 (S x2) = S x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ae [thy_expl]: "max2 (max2 x1 y1) (S x1) = max2 y1 (S x1)"
by (hipster_induct_schemes max2.simps)


end

