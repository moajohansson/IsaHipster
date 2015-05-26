theory prop_07
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
  | "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  (*hipster qrev plus length *)

(*hipster qrev*)
lemma lemma_a [thy_expl]: "qrev (qrev x2 y2) Nil2 = qrev y2 x2"
by (hipster_induct_schemes qrev.simps)

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

lemma lemma_az [thy_expl]: "plus (S x2) (plus y2 z2) = plus (plus y2 z2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ba [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus x2 y2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bb [thy_expl]: "plus (plus x2 x2) (S y2) = plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bc [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus y2 x2) (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bd [thy_expl]: "plus (S x2) (plus x2 y2) = plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_be [thy_expl]: "plus (S x2) (plus y2 x2) = plus (plus y2 x2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bf [thy_expl]: "plus (S x2) (S y2) = plus (S y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bg [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_bh [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

  theorem x0 :
    "(length (qrev x y)) = (plus (length x) (length y))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
