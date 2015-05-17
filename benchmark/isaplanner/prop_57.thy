theory prop_57
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster take minus drop *)
lemma lemma_a [thy_expl]: "prop_57.minus x2 x2 = Z"
by (hipster_induct_schemes prop_57.minus.simps)

lemma lemma_aa [thy_expl]: "prop_57.minus x3 Z = x3"
by (hipster_induct_schemes prop_57.minus.simps)

lemma lemma_ab [thy_expl]: "prop_57.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_57.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_57.minus (prop_57.minus x3 y3) (prop_57.minus y3 x3) =
prop_57.minus x3 y3"
by (hipster_induct_schemes prop_57.minus.simps)

lemma lemma_ae [thy_expl]: "prop_57.minus (prop_57.minus x3 y3) (S Z) = prop_57.minus x3 (S y3)"
by (hipster_induct_schemes prop_57.minus.simps)

lemma lemma_af [thy_expl]: "prop_57.minus (prop_57.minus x4 y4) x4 = Z"
by (hipster_induct_schemes prop_57.minus.simps)

lemma lemma_ag [thy_expl]: "prop_57.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_57.drop.simps)

lemma lemma_ah [thy_expl]: "prop_57.drop (S Z) (prop_57.drop x3 y3) = prop_57.drop (S x3) y3"
by (hipster_induct_schemes prop_57.drop.simps)

lemma unknown [thy_expl]: "prop_57.drop x (prop_57.drop y z) = prop_57.drop y (prop_57.drop x z)"
oops

lemma unknown [thy_expl]: "prop_57.drop (S x) (prop_57.drop y z) =
prop_57.drop (S y) (prop_57.drop x z)"
oops

hipster take
lemma lemma_ai [thy_expl]: "prop_57.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_aj [thy_expl]: "prop_57.take x3 (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)

lemma lemma_ak [thy_expl]: "prop_57.take (S x3) (prop_57.take x3 y3) = prop_57.take x3 y3"
by (hipster_induct_schemes prop_57.take.simps)

lemma unknown [thy_expl]: "prop_57.take x (prop_57.take y z) = prop_57.take y (prop_57.take x z)"
oops

  theorem x0 :
    "(drop n (take m xs)) = (take (minus m n) (drop n xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
