theory prop_34
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S z) y = plus y (mult z y)"
  fun mult2 :: "Nat => Nat => Nat => Nat" where
  "mult2 (Z) y z = z"
  | "mult2 (S x2) y z = mult2 x2 y (plus y z)"
  (*hipster plus mult2 mult *)

(*hipster plus*)
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

hipster mult plus
lemma lemma_aj [thy_expl]: "mult x2 Z = Z"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ak [thy_expl]: "mult (plus x9 x9) y9 = mult x9 (plus y9 y9)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_al [thy_expl]: "plus (mult x9 y9) (mult x9 z9) = mult x9 (plus y9 z9)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_am [thy_expl]: "plus (mult x10 x10) (mult y10 y10) = plus (mult y10 y10) (mult x10 x10)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_an [thy_expl]: "mult x2 (S Z) = x2"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ao [thy_expl]: "mult (mult x10 x10) (plus x10 x10) = mult (plus x10 x10) (mult x10 x10)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ap [thy_expl]: "mult (S x10) (plus x10 x10) = mult (plus x10 x10) (S x10)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_aq [thy_expl]: "mult x10 y10 = mult y10 x10"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ar [thy_expl]: "mult x10 (mult y10 z10) = mult y10 (mult x10 z10)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_as [thy_expl]: "mult (plus x9 x9) (mult y9 y9) = mult (mult y9 x9) (plus y9 y9)"
by (hipster_induct_schemes mult.simps plus.simps)



  theorem x0 :
    "(mult x y) = (mult2 x y Z)"
    apply(hipster_induct_schemes mult.simps mult2.simps Nat.exhaust)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
