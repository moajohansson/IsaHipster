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

hipster qrev
lemma lemma_a [thy_expl]: "qrev (qrev x2 y2) Nil2 = qrev y2 x2"
by (hipster_induct_schemes prop_07.qrev.simps)

lemma lemma_ag [thy_expl]: "prop_07.plus x2 Z = x2"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_ah [thy_expl]: "prop_07.plus (prop_07.plus x2 y2) z2 = prop_07.plus x2 (prop_07.plus y2 z2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_ai [thy_expl]: "prop_07.plus x2 (S y2) = S (prop_07.plus x2 y2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_aj [thy_expl]: "prop_07.plus x2 (prop_07.plus y2 x2) = prop_07.plus y2 (prop_07.plus x2 x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_ak [thy_expl]: "prop_07.plus x2 (prop_07.plus y2 y2) = prop_07.plus y2 (prop_07.plus y2 x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_al [thy_expl]: "prop_07.plus x2 (S y2) = S (prop_07.plus y2 x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_am [thy_expl]: "prop_07.plus (prop_07.plus x2 y2) x2 = prop_07.plus x2 (prop_07.plus x2 y2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_an [thy_expl]: "prop_07.plus (S x2) y2 = S (prop_07.plus y2 x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_ao [thy_expl]: "prop_07.plus (prop_07.plus x3 y3) (prop_07.plus x3 z3) =
prop_07.plus (prop_07.plus x3 z3) (prop_07.plus x3 y3)"
by (hipster_induct_schemes )

lemma lemma_ap [thy_expl]: "prop_07.plus (prop_07.plus x2 y2) (prop_07.plus z2 y2) =
prop_07.plus (prop_07.plus x2 z2) (prop_07.plus y2 y2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_aq [thy_expl]: "prop_07.plus (prop_07.plus x3 y3) (prop_07.plus z3 z3) =
prop_07.plus (prop_07.plus x3 z3) (prop_07.plus z3 y3)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_az [thy_expl]: "prop_07.plus (S x2) (prop_07.plus y2 z2) =
prop_07.plus (prop_07.plus y2 z2) (S x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_ba [thy_expl]: "prop_07.plus (prop_07.plus x2 x2) (prop_07.plus y2 y2) =
prop_07.plus (prop_07.plus x2 y2) (prop_07.plus x2 y2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bb [thy_expl]: "prop_07.plus (prop_07.plus x2 x2) (S y2) =
prop_07.plus (prop_07.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bc [thy_expl]: "prop_07.plus (prop_07.plus x2 x2) (prop_07.plus y2 y2) =
prop_07.plus (prop_07.plus y2 x2) (prop_07.plus y2 x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bd [thy_expl]: "prop_07.plus (S x2) (prop_07.plus x2 y2) =
prop_07.plus (prop_07.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_be [thy_expl]: "prop_07.plus (S x2) (prop_07.plus y2 x2) =
prop_07.plus (prop_07.plus y2 x2) (S x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bf [thy_expl]: "prop_07.plus (S x2) (S y2) = prop_07.plus (S y2) (S x2)"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bg [thy_expl]: "prop_07.plus x2 y2 = prop_07.plus y2 x2"
by (hipster_induct_schemes prop_07.plus.simps)

lemma lemma_bh [thy_expl]: "prop_07.plus x2 (prop_07.plus y2 z2) = prop_07.plus y2 (prop_07.plus x2 z2)"
by (hipster_induct_schemes prop_07.plus.simps)

  theorem x0 :
    "(length (qrev x y)) = (plus (length x) (length y))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
