theory prop_26
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S z)) = S (half z)"
  (*hipster plus half *)

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

lemma lemma_ag [thy_expl]: "plus (plus x2 y2) (plus x2 z2) =
plus (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) (plus z2 x2) = plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus z2 x2)"
by (hipster_induct_schemes plus.simps)

(*hipster plus half
lemma lemma_aj [thy_expl]: "half (plus x1 x1) = x1"
by (hipster_induct_schemes plus.simps half.simps)*)

  theorem x0 :
    "(half (plus x y)) = (half (plus y x))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
