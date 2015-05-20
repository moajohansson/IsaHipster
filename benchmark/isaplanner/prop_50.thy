theory prop_50
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
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
  | "butlast (Cons2 y (Nil2)) = Nil2"
  | "butlast (Cons2 y (Cons2 x2 x3)) =
       Cons2 y (butlast (Cons2 x2 x3))"
  (*hipster take minus len butlast *)
lemma lemma_a [thy_expl]: "prop_50.minus x2 x2 = Z"
by (hipster_induct_schemes prop_50.minus.simps)

lemma lemma_aa [thy_expl]: "prop_50.minus x3 Z = x3"
by (hipster_induct_schemes prop_50.minus.simps)

lemma lemma_ab [thy_expl]: "prop_50.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_50.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_50.minus (prop_50.minus x3 y3) (prop_50.minus y3 x3) =
prop_50.minus x3 y3"
by (hipster_induct_schemes prop_50.minus.simps)

lemma lemma_ae [thy_expl]: "prop_50.minus (prop_50.minus x3 y3) (S Z) = prop_50.minus x3 (S y3)"
by (hipster_induct_schemes prop_50.minus.simps)

lemma lemma_af [thy_expl]: "prop_50.minus (prop_50.minus x4 y4) x4 = Z"
apply(induction x4 y4 rule: minus.induct)
apply(simp_all)
sledgehammer
apply (metis minus.simps  thy_expl)
apply(simp_all)
apply (metis minus.simps  thy_expl)
done (*
by (hipster_induct_schemes prop_50.minus.simps)*)

  theorem x0 :
    "(butlast xs) = (take (minus (len xs) (S Z)) xs)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
