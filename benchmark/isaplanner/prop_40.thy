theory prop_40
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  (*hipster take *)
hipster take
lemma lemma_a [thy_expl]: "prop_40.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_40.take.simps)

lemma lemma_aa [thy_expl]: "prop_40.take x3 (prop_40.take x3 y3) = prop_40.take x3 y3"
by (hipster_induct_schemes prop_40.take.simps)

lemma lemma_ab [thy_expl]: "prop_40.take (S x3) (prop_40.take x3 y3) = prop_40.take x3 y3"
by (hipster_induct_schemes prop_40.take.simps)

lemma unknown [thy_expl]: "prop_40.take x (prop_40.take y z) = prop_40.take y (prop_40.take x z)"
oops

  theorem x0 :
    "(take Z xs) = (Nil2)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
