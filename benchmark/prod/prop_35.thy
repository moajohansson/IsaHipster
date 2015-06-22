theory prop_35
imports Main
        "../../IsaHipster"
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
  fun qexp :: "Nat => Nat => Nat => Nat" where
  "qexp x (Z) z = z"
  | "qexp x (S n) z = qexp x n (mult x z)"
  fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
  | "exp x (S n) = mult x (exp x n)"
  (*hipster plus one mult qexp exp *)

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

lemma lemma_ag [thy_expl]: "plus (plus x2 y2) (plus x2 z2) =
plus (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) (plus z2 x2) = plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus z2 x2)"
by (hipster_induct_schemes plus.simps)

(*hipster plus one*)
lemma lemma_aj [thy_expl]: "plus x one = S x"
by (hipster_induct_schemes plus.simps one_def)

lemma lemma_ak [thy_expl]: "plus one x = S x"
by (hipster_induct_schemes plus.simps one_def)

hipster mult plus one
lemma lemma_al [thy_expl]: "mult x2 Z = Z"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_am [thy_expl]: "mult x10 (S y10) = prop_35.plus x10 (mult x10 y10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_an [thy_expl]: "mult x11 (prop_35.plus y11 y11) = mult y11 (prop_35.plus x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ao [thy_expl]: "mult x11 (S y11) = prop_35.plus x11 (mult y11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ap [thy_expl]: "mult (prop_35.plus x11 y11) x11 = mult x11 (prop_35.plus x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_aq [thy_expl]: "mult (prop_35.plus x10 y10) y10 = mult y10 (prop_35.plus x10 y10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ar [thy_expl]: "mult (mult x10 y10) x10 = mult x10 (mult x10 y10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_as [thy_expl]: "prop_35.plus (mult x11 x11) y11 = prop_35.plus y11 (mult x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_at [thy_expl]: "mult (prop_35.plus x10 x10) y10 = mult x10 (prop_35.plus y10 y10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_au [thy_expl]: "mult (mult x11 x11) y11 = mult y11 (mult x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_av [thy_expl]: "prop_35.plus (mult x10 y10) (mult x10 z10) = mult x10 (prop_35.plus y10 z10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_aw [thy_expl]: "prop_35.plus (mult x10 y10) (mult y10 z10) = mult y10 (prop_35.plus x10 z10)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ax [thy_expl]: "prop_35.plus (mult x11 y11) (mult x11 z11) = mult x11 (prop_35.plus z11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ay [thy_expl]: "prop_35.plus (mult x11 y11) (mult z11 x11) = mult x11 (prop_35.plus z11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_az [thy_expl]: "mult (prop_35.plus x11 y11) (prop_35.plus x11 z11) =
mult (prop_35.plus x11 z11) (prop_35.plus x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_ba [thy_expl]: "mult (prop_35.plus x11 y11) (prop_35.plus z11 x11) =
mult (prop_35.plus z11 x11) (prop_35.plus x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bb [thy_expl]: "mult (prop_35.plus x11 y11) (prop_35.plus z11 y11) =
mult (prop_35.plus z11 y11) (prop_35.plus x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bc [thy_expl]: "mult (mult x11 y11) (prop_35.plus x11 z11) =
mult (prop_35.plus x11 z11) (mult x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bd [thy_expl]: "mult (mult x11 y11) (prop_35.plus y11 z11) =
mult (prop_35.plus y11 z11) (mult x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_be [thy_expl]: "mult (mult x11 y11) (prop_35.plus z11 y11) =
mult (prop_35.plus z11 y11) (mult x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bf [thy_expl]: "mult (mult x11 y11) (prop_35.plus z11 x11) =
mult (prop_35.plus z11 x11) (mult x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bg [thy_expl]: "mult (mult x11 y11) (mult z11 x11) = mult (mult z11 x11) (mult x11 y11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bh [thy_expl]: "prop_35.plus (prop_35.plus x11 x11) (prop_35.plus y11 z11) =
prop_35.plus (prop_35.plus y11 z11) (prop_35.plus x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bi [thy_expl]: "mult (prop_35.plus x11 x11) (prop_35.plus y11 z11) =
mult (prop_35.plus y11 z11) (prop_35.plus x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bj [thy_expl]: "mult (prop_35.plus x11 x11) (mult y11 z11) =
mult (mult y11 z11) (prop_35.plus x11 x11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bk [thy_expl]: "mult x11 y11 = mult y11 x11"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)

lemma lemma_bl [thy_expl]: "mult x11 (mult y11 z11) = mult y11 (mult x11 z11)"
by (hipster_induct_schemes prop_35.mult.simps prop_35.plus.simps prop_35.one_def)


  theorem x0 :
    "(exp x y) = (qexp x y one)"

    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
