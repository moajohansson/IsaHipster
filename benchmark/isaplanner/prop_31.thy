theory prop_31
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
  | "min2 (S z) (Z) = Z"
  | "min2 (S z) (S y1) = S (min2 z y1)"
  (*hipster min2 *)

lemma lemma_a [thy_expl]: "min2 x x = x"
by (hipster_induct_schemes min2.simps)

lemma lemma_aa [thy_expl]: "min2 x Z = Z"
by (hipster_induct_schemes min2.simps)

lemma lemma_ab [thy_expl]: "min2 x (min2 x y) = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ac [thy_expl]: "min2 x (min2 y x) = min2 y x"
by (hipster_induct_schemes min2.simps)

lemma lemma_ad [thy_expl]: "min2 (min2 x y) x = min2 x y"
by (hipster_induct_schemes min2.simps)

lemma lemma_ae []: "min2 (S x) y = min2 y (S x)"
by (hipster_induct_schemes min2.simps)

lemma lemma_af [thy_expl]: "min2 x y = min2 y x"
by (hipster_induct_schemes min2.simps)

  theorem x0 :
    "(min2 (min2 a b) c) = (min2 a (min2 b c))"
    apply(induction a b arbitrary: c rule: min2.induct)
    apply(simp_all add: thy_expl)
    by (metis min2.simps Nat.exhaust thy_expl)
    (*by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
