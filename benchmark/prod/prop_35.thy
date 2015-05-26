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


  theorem x0 :
    "(exp x y) = (qexp x y one)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
