theory prop_81
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster take plus drop *)

lemma lemma_ag [thy_expl]: "prop_81.plus x2 Z = x2"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_ah [thy_expl]: "prop_81.plus (prop_81.plus x2 y2) z2 = prop_81.plus x2 (prop_81.plus y2 z2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_ai [thy_expl]: "prop_81.plus x2 (S y2) = S (prop_81.plus x2 y2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_aj [thy_expl]: "prop_81.plus x2 (prop_81.plus y2 x2) = prop_81.plus y2 (prop_81.plus x2 x2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_ak [thy_expl]: "prop_81.plus x2 (prop_81.plus y2 y2) = prop_81.plus y2 (prop_81.plus y2 x2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_al [thy_expl]: "prop_81.plus x2 (S y2) = S (prop_81.plus y2 x2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_am [thy_expl]: "prop_81.plus (prop_81.plus x2 y2) x2 = prop_81.plus x2 (prop_81.plus x2 y2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_an [thy_expl]: "prop_81.plus (S x2) y2 = S (prop_81.plus y2 x2)"
by (hipster_induct_schemes prop_81.plus.simps)

lemma lemma_ao [thy_expl]: "prop_81.plus (prop_81.plus x3 y3) (prop_81.plus x3 z3) =
prop_81.plus (prop_81.plus x3 z3) (prop_81.plus x3 y3)"
by (hipster_induct_schemes )

lemma lemma_a [thy_expl]: "prop_56.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_56.drop.simps)

lemma lemma_aa [thy_expl]: "prop_56.drop (S Z) (prop_56.drop x3 y3) = prop_56.drop (S x3) y3"
by (hipster_induct_schemes prop_56.drop.simps)

lemma lemma_tai [thy_expl]: "prop_57.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_taj [thy_expl]: "prop_57.take x3 (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_tak [thy_expl]: "prop_57.take (S x3) (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)


  theorem x0 :
    "(take n (drop m xs)) = (drop m (take (plus n m) xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
