theory mult
imports Main
        "../data/Natu"
        "../funcs/plus"
        "../../IsaHipster"
begin

fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
| "mult (S z) y = plus y (mult z y)"

(*hipster mult plus*)
lemma lemma_aj [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ak [thy_expl]: "mult x2 Z = Z"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_al [thy_expl]: "mult x1 (S y1) = plus x1 (mult x1 y1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_am [thy_expl]: "mult x2 (plus y2 y2) = mult y2 (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_an [thy_expl]: "mult x2 (S y2) = plus x2 (mult y2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ao [thy_expl]: "mult (plus x2 y2) x2 = mult x2 (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ap [thy_expl]: "mult (mult x1 y1) x1 = mult x1 (mult x1 y1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_aq [thy_expl]: "mult (plus x2 x2) y2 = mult x2 (plus y2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ar [thy_expl]: "mult (mult x2 x2) y2 = mult y2 (mult x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_as [thy_expl]: "plus (mult x1 y1) (mult y1 z1) = mult y1 (plus x1 z1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_at [thy_expl]: "plus (mult x2 y2) (mult z2 x2) = mult x2 (plus z2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_au [thy_expl]: "mult (plus x2 y2) (plus x2 z2) = mult (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_av [thy_expl]: "mult (plus x2 y2) (plus z2 y2) = mult (plus z2 y2) (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_aw [thy_expl]: "mult (mult x2 y2) (plus x2 z2) = mult (plus x2 z2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ax [thy_expl]: "mult (mult x2 y2) (plus y2 z2) = mult (plus y2 z2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ay [thy_expl]: "mult (mult x2 y2) (mult z2 x2) = mult (mult z2 x2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_az [thy_expl]: "mult (plus x2 x2) (plus y2 z2) = mult (plus y2 z2) (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ba [thy_expl]: "mult (plus x2 x2) (mult y2 z2) = mult (mult y2 z2) (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bb [thy_expl]: "mult (S x2) (S y2) = mult (S y2) (S x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bc [thy_expl]: "mult x2 y2 = mult y2 x2"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bd [thy_expl]: "mult x2 (mult y2 z2) = mult y2 (mult x2 z2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_be [thy_expl]: "plus (mult x1 y1) (mult x1 z1) = mult x1 (plus y1 z1)"
by (hipster_induct_schemes mult.simps plus.simps)
 
end

