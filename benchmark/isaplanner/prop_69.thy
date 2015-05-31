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
by (hipster_induct_schemes le.simps)

lemma lemma_ac [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)


lemma lemma_ag [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) z2 = plus x2 (plus y2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aj [thy_expl]: "plus x2 (plus y2 x2) = plus y2 (plus x2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ak [thy_expl]: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_al [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_am [thy_expl]: "plus (plus x2 y2) x2 = plus x2 (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_an [thy_expl]: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ao [thy_expl]: "plus (plus x3 y3) (plus x3 z3) = plus (plus x3 z3) (plus x3 y3)"
by (hipster_induct_schemes )

lemma lemma_ap [thy_expl]: "plus (plus x2 y2) (plus z2 y2) = plus (plus x2 z2) (plus y2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aq [thy_expl]: "plus (plus x3 y3) (plus z3 z3) = plus (plus x3 z3) (plus z3 y3)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ar [thy_expl]: "plus (plus x2 y2) (S z2) = plus (plus x2 z2) (S y2)"
by (hipster_induct_schemes plus.simps)
(*
lemma lemma_as [thy_expl]: "plus (plus x2 y2) (plus z2 x2) =
plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_at [thy_expl]: "plus (plus x2 y2) (plus z2 y2) =
plus (plus z2 x2) (plus y2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_au [thy_expl]: "plus (plus x3 y3) (plus z3 z3) =
plus (plus z3 x3) (plus z3 y3)"
by (hipster_induct_schemes plus.simps)

lemma lemma_av [thy_expl]: "plus (plus x2 y2) (S z2) =
plus (plus z2 x2) (S y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aw [thy_expl]: "plus (plus x2 x2) (plus y2 z2) =
plus (plus x2 y2) (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ax [thy_expl]: "plus (plus x2 x2) (plus y2 z2) =
plus (plus y2 x2) (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ay [thy_expl]: "plus (S x2) (plus y2 z2) =
plus (plus y2 x2) (S z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_az [thy_expl]: "plus (S x2) (plus y2 z2) =
plus (plus y2 z2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ba [thy_expl]: "plus (plus x2 x2) (plus y2 y2) =
plus (plus x2 y2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bb [thy_expl]: "plus (plus x2 x2) (S y2) =
plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bc [thy_expl]: "plus (plus x2 x2) (plus y2 y2) =
plus (plus y2 x2) (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bd [thy_expl]: "plus (S x2) (plus x2 y2) =
plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_be [thy_expl]: "plus (S x2) (plus y2 x2) =
plus (plus y2 x2) (S x2)"
by (hipster_induct_schemes plus.simps)
*)
lemma lemma_bf [thy_expl]: "plus (S x2) (S y2) = plus (S y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bg [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_bh [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

  theorem x0 :
    "le n (plus m n)"
    by (hipster_induct_schemes le.simps)
end
