theory plus
imports Main
        "../data/Natu"
        "../../IsaHipster"
begin

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

(*hipster plus*)
lemma lemma_a [thy_expl]: "plus.plus x2 Z = x2"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_aa [thy_expl]: "plus.plus (plus.plus x2 y2) z2 = plus.plus x2 (plus.plus y2 z2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ab [thy_expl]: "plus.plus x2 (S y2) = S (plus.plus x2 y2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ac [thy_expl]: "plus.plus x1 (plus.plus y1 x1) = plus.plus y1 (plus.plus x1 x1)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ad [thy_expl]: "plus.plus x2 (plus.plus y2 y2) = plus.plus y2 (plus.plus y2 x2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ae [thy_expl]: "plus.plus x2 (S y2) = S (plus.plus y2 x2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_af [thy_expl]: "plus.plus (S x2) y2 = S (plus.plus y2 x2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ag [thy_expl]: "plus.plus (plus.plus x2 y2) (plus.plus x2 z2) =
plus.plus (plus.plus x2 z2) (plus.plus x2 y2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ah [thy_expl]: "plus.plus (plus.plus x2 y2) (plus.plus z2 x2) =
plus.plus (plus.plus z2 x2) (plus.plus x2 y2)"
by (hipster_induct_schemes plus.plus.simps)

lemma lemma_ai [thy_expl]: "plus.plus x2 (plus.plus y2 z2) = plus.plus y2 (plus.plus z2 x2)"
by (hipster_induct_schemes plus.plus.simps)

end

