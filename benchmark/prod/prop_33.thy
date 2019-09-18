theory prop_33
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  definition one :: "Nat" where
  "one = S Z"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S z) y = plus y (mult z y)"
  fun qfac :: "Nat => Nat => Nat" where
  "qfac (Z) y = y"
  | "qfac (S z) y = qfac z (mult (S z) y)"
  fun fac :: "Nat => Nat" where
  "fac (Z) = S Z"
  | "fac (S y) = mult (S y) (fac y)"
  (*hipster plus one mult qfac fac *)

(*hipster plus*)
hipster plus one
lemma lemma_a [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_aa [thy_expl]: "plus (plus x1 y1) z1 = plus x1 (plus y1 z1)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ab [thy_expl]: "plus x1 (S y1) = S (plus x1 y1)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ac [thy_expl]: "plus x6 (plus y6 x6) = plus y6 (plus x6 x6)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ad [thy_expl]: "plus x7 (plus y7 y7) = plus y7 (plus y7 x7)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ae [thy_expl]: "plus x7 (S y7) = S (plus y7 x7)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_af [thy_expl]: "plus (S x7) y7 = S (plus y7 x7)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ag [thy_expl]: "plus (plus x7 y7) (plus x7 z7) =
plus (plus x7 z7) (plus x7 y7)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ah [thy_expl]: "plus (plus x7 y7) (plus z7 x7) =
plus (plus z7 x7) (plus x7 y7)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ai [thy_expl]: "plus (plus x6 x6) (plus y6 z6) =
plus (plus x6 y6) (plus x6 z6)"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_aj [thy_expl]: "plus x7 y7 = plus y7 x7"
by (hipster_induct_schemes plus.simps one_def)

hipster mult plus one

(*
lemma lemma_a [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_aa [thy_expl]: "plus (plus x2 y2) z2 = plus x2 (plus y2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ab [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ac [thy_expl]: "plus x1 (plus y1 x1) = plus y1 (plus x1 x1)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ad [thy_expl]: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ae [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_af [thy_expl]: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ag [thy_expl]: "plus (plus x2 y2) (plus x2 z2) = plus (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) (plus z2 x2) = plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus z2 x2)"
by (hipster_induct_schemes plus.simps)

(*hipster plus one*)
lemma lemma_ajo [thy_expl]: "plus x one = S x"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ako [thy_expl]: "plus one x = S x"
by (hipster_induct_schemes plus.simps one_def)

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
by (hipster_induct_schemes mult.simps plus.simps Nat.exhaust)

lemma lemma_be [thy_expl]: "plus (mult x1 y1) (mult x1 z1) = mult x1 (plus y1 z1)"
by (hipster_induct_schemes mult.simps plus.simps)
*)

  theorem x0 :
    "(fac x) = (qfac x one)"
    apply(induction x rule: fac.induct)
    apply(simp_all)
    apply(metis thy_expl fac.simps qfac.simps mult.simps plus.simps)
    apply (hipster_induct_schemes mult.simps plus.simps fac.simps qfac.simps Nat.exhaust one_def)

    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
