theory prop_69
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  (*hipster plus le *)

lemma lemma_ab [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes prop_69.le.simps)

lemma lemma_ac [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes prop_69.le.simps)

lemma lemma_ad [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes prop_69.le.simps)


lemma lemma_ag [thy_expl]: "prop_69.plus x2 Z = x2"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ah [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) z2 = prop_69.plus x2 (prop_69.plus y2 z2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ai [thy_expl]: "prop_69.plus x2 (S y2) = S (prop_69.plus x2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_aj [thy_expl]: "prop_69.plus x2 (prop_69.plus y2 x2) = prop_69.plus y2 (prop_69.plus x2 x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ak [thy_expl]: "prop_69.plus x2 (prop_69.plus y2 y2) = prop_69.plus y2 (prop_69.plus y2 x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_al [thy_expl]: "prop_69.plus x2 (S y2) = S (prop_69.plus y2 x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_am [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) x2 = prop_69.plus x2 (prop_69.plus x2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_an [thy_expl]: "prop_69.plus (S x2) y2 = S (prop_69.plus y2 x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ao [thy_expl]: "prop_69.plus (prop_69.plus x3 y3) (prop_69.plus x3 z3) =
prop_69.plus (prop_69.plus x3 z3) (prop_69.plus x3 y3)"
by (hipster_induct_schemes )

lemma lemma_ap [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) (prop_69.plus z2 y2) =
prop_69.plus (prop_69.plus x2 z2) (prop_69.plus y2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_aq [thy_expl]: "prop_69.plus (prop_69.plus x3 y3) (prop_69.plus z3 z3) =
prop_69.plus (prop_69.plus x3 z3) (prop_69.plus z3 y3)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ar [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) (S z2) =
prop_69.plus (prop_69.plus x2 z2) (S y2)"
by (hipster_induct_schemes prop_69.plus.simps)
(*
lemma lemma_as [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) (prop_69.plus z2 x2) =
prop_69.plus (prop_69.plus z2 x2) (prop_69.plus x2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_at [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) (prop_69.plus z2 y2) =
prop_69.plus (prop_69.plus z2 x2) (prop_69.plus y2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_au [thy_expl]: "prop_69.plus (prop_69.plus x3 y3) (prop_69.plus z3 z3) =
prop_69.plus (prop_69.plus z3 x3) (prop_69.plus z3 y3)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_av [thy_expl]: "prop_69.plus (prop_69.plus x2 y2) (S z2) =
prop_69.plus (prop_69.plus z2 x2) (S y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_aw [thy_expl]: "prop_69.plus (prop_69.plus x2 x2) (prop_69.plus y2 z2) =
prop_69.plus (prop_69.plus x2 y2) (prop_69.plus x2 z2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ax [thy_expl]: "prop_69.plus (prop_69.plus x2 x2) (prop_69.plus y2 z2) =
prop_69.plus (prop_69.plus y2 x2) (prop_69.plus x2 z2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ay [thy_expl]: "prop_69.plus (S x2) (prop_69.plus y2 z2) =
prop_69.plus (prop_69.plus y2 x2) (S z2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_az [thy_expl]: "prop_69.plus (S x2) (prop_69.plus y2 z2) =
prop_69.plus (prop_69.plus y2 z2) (S x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_ba [thy_expl]: "prop_69.plus (prop_69.plus x2 x2) (prop_69.plus y2 y2) =
prop_69.plus (prop_69.plus x2 y2) (prop_69.plus x2 y2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_bb [thy_expl]: "prop_69.plus (prop_69.plus x2 x2) (S y2) =
prop_69.plus (prop_69.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_bc [thy_expl]: "prop_69.plus (prop_69.plus x2 x2) (prop_69.plus y2 y2) =
prop_69.plus (prop_69.plus y2 x2) (prop_69.plus y2 x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_bd [thy_expl]: "prop_69.plus (S x2) (prop_69.plus x2 y2) =
prop_69.plus (prop_69.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_be [thy_expl]: "prop_69.plus (S x2) (prop_69.plus y2 x2) =
prop_69.plus (prop_69.plus y2 x2) (S x2)"
by (hipster_induct_schemes prop_69.plus.simps)
*)
lemma lemma_bf [thy_expl]: "prop_69.plus (S x2) (S y2) = prop_69.plus (S y2) (S x2)"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_bg [thy_expl]: "prop_69.plus x2 y2 = prop_69.plus y2 x2"
by (hipster_induct_schemes prop_69.plus.simps)

lemma lemma_bh [thy_expl]: "prop_69.plus x2 (prop_69.plus y2 z2) = prop_69.plus y2 (prop_69.plus x2 z2)"
by (hipster_induct_schemes prop_69.plus.simps)

  theorem x0 :
    "le n (plus m n)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
