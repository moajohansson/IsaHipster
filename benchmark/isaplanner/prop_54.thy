theory prop_54
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  (*hipster plus minus *)
(*hipster minus*)
lemma lemma_a [thy_expl]: "prop_54.minus x2 x2 = Z"
apply (hipster_induct_schemes prop_54.minus.simps)
done

lemma lemma_aa [thy_expl]: "prop_54.minus x3 Z = x3"
by (hipster_induct_schemes prop_54.minus.simps)

lemma lemma_ab [thy_expl]: "prop_54.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_54.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_54.minus (prop_54.minus x3 y3) (prop_54.minus y3 x3) =
prop_54.minus x3 y3"
by (hipster_induct_schemes prop_54.minus.simps)

lemma lemma_ae [thy_expl]: "prop_54.minus (prop_54.minus x3 y3) (S Z) = prop_54.minus x3 (S y3)"
by (hipster_induct_schemes prop_54.minus.simps)

lemma lemma_af [thy_expl]: "prop_54.minus (prop_54.minus x4 y4) x4 = Z"

by (hipster_induct_schemes prop_54.minus.simps)

(*hipster plus*)
lemma lemma_ag [thy_expl]: "prop_54.plus x2 Z = x2"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ah [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) z2 = prop_54.plus x2 (prop_54.plus y2 z2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ai [thy_expl]: "prop_54.plus x2 (S y2) = S (prop_54.plus x2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_aj [thy_expl]: "prop_54.plus x2 (prop_54.plus y2 x2) = prop_54.plus y2 (prop_54.plus x2 x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ak [thy_expl]: "prop_54.plus x2 (prop_54.plus y2 y2) = prop_54.plus y2 (prop_54.plus y2 x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_al [thy_expl]: "prop_54.plus x2 (S y2) = S (prop_54.plus y2 x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_am [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) x2 = prop_54.plus x2 (prop_54.plus x2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_an [thy_expl]: "prop_54.plus (S x2) y2 = S (prop_54.plus y2 x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ao [thy_expl]: "prop_54.plus (prop_54.plus x3 y3) (prop_54.plus x3 z3) =
prop_54.plus (prop_54.plus x3 z3) (prop_54.plus x3 y3)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ap [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) (prop_54.plus z2 y2) =
prop_54.plus (prop_54.plus x2 z2) (prop_54.plus y2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_aq [thy_expl]: "prop_54.plus (prop_54.plus x3 y3) (prop_54.plus z3 z3) =
prop_54.plus (prop_54.plus x3 z3) (prop_54.plus z3 y3)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ar [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) (S z2) =
prop_54.plus (prop_54.plus x2 z2) (S y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_as [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) (prop_54.plus z2 x2) =
prop_54.plus (prop_54.plus z2 x2) (prop_54.plus x2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_at [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) (prop_54.plus z2 y2) =
prop_54.plus (prop_54.plus z2 x2) (prop_54.plus y2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_au [thy_expl]: "prop_54.plus (prop_54.plus x3 y3) (prop_54.plus z3 z3) =
prop_54.plus (prop_54.plus z3 x3) (prop_54.plus z3 y3)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_av [thy_expl]: "prop_54.plus (prop_54.plus x2 y2) (S z2) =
prop_54.plus (prop_54.plus z2 x2) (S y2)"
by (hipster_induct_schemes prop_54.plus.simps)
(*
apply(induction x2 y2 rule: plus.induct)
apply(tactic {* Ind_Tacs.simp_all @{context} []*})
apply(tactic {* ALLGOALS (Ind_Tacs.timed_metis_tac @{context} @{thms thy_expl} )*})
apply(tactic {* Ind_Tacs.simp_or_metis @{context} ([],@{thms thy_expl} )*})
apply(metis plus.simps thy_expl)*)
(*by (hipster_induct_schemes prop_54.plus.simps)*)

lemma lemma_aw [thy_expl]: "prop_54.plus (prop_54.plus x2 x2) (prop_54.plus y2 z2) =
prop_54.plus (prop_54.plus x2 y2) (prop_54.plus x2 z2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ax [thy_expl]: "prop_54.plus (prop_54.plus x2 x2) (prop_54.plus y2 z2) =
prop_54.plus (prop_54.plus y2 x2) (prop_54.plus x2 z2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ay [thy_expl]: "prop_54.plus (S x2) (prop_54.plus y2 z2) =
prop_54.plus (prop_54.plus y2 x2) (S z2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_az [thy_expl]: "prop_54.plus (S x2) (prop_54.plus y2 z2) =
prop_54.plus (prop_54.plus y2 z2) (S x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_ba [thy_expl]: "prop_54.plus (prop_54.plus x2 x2) (prop_54.plus y2 y2) =
prop_54.plus (prop_54.plus x2 y2) (prop_54.plus x2 y2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bb [thy_expl]: "prop_54.plus (prop_54.plus x2 x2) (S y2) =
prop_54.plus (prop_54.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bc [thy_expl]: "prop_54.plus (prop_54.plus x2 x2) (prop_54.plus y2 y2) =
prop_54.plus (prop_54.plus y2 x2) (prop_54.plus y2 x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bd [thy_expl]: "prop_54.plus (S x2) (prop_54.plus x2 y2) =
prop_54.plus (prop_54.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_be [thy_expl]: "prop_54.plus (S x2) (prop_54.plus y2 x2) =
prop_54.plus (prop_54.plus y2 x2) (S x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bf [thy_expl]: "prop_54.plus (S x2) (S y2) = prop_54.plus (S y2) (S x2)"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bg [thy_expl]: "prop_54.plus x2 y2 = prop_54.plus y2 x2"
by (hipster_induct_schemes prop_54.plus.simps)

lemma lemma_bh [thy_expl]: "prop_54.plus x2 (prop_54.plus y2 z2) = prop_54.plus y2 (prop_54.plus x2 z2)"
by (hipster_induct_schemes prop_54.plus.simps)

  theorem x0 :
    "(minus (plus m n) n) = m"
    by (hipster_induct_schemes plus.simps minus.simps)
    (*
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
