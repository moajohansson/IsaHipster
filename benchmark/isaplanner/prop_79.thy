theory prop_79
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  (*hipster minus *)
lemma lemma_a [thy_expl]: "prop_79.minus x2 x2 = Z"
by (hipster_induct_schemes prop_79.minus.simps)

lemma lemma_aa [thy_expl]: "prop_79.minus x3 Z = x3"
by (hipster_induct_schemes prop_79.minus.simps)

lemma lemma_ab [thy_expl]: "prop_79.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_79.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_79.minus (prop_79.minus x3 y3) (prop_79.minus y3 x3) =
prop_79.minus x3 y3"
by (hipster_induct_schemes prop_79.minus.simps)

lemma lemma_ae [thy_expl]: "prop_79.minus (prop_79.minus x3 y3) (S Z) = prop_79.minus x3 (S y3)"
by (hipster_induct_schemes prop_79.minus.simps)

lemma lemma_af [thy_expl]: "prop_79.minus (prop_79.minus x4 y4) x4 = Z"
by (hipster_induct_schemes prop_79.minus.simps)

  theorem x0 :
    "(minus (minus (S m) n) (S k)) = (minus (minus m n) k)"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
