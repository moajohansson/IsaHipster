theory prop_08
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster drop *)
lemma lemma_a [thy_expl]: "prop_08.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_08.drop.simps)

lemma lemma_aa [thy_expl]: "prop_08.drop (S Z) (prop_08.drop x3 y3) = prop_08.drop (S x3) y3"
by (hipster_induct_schemes prop_08.drop.simps)

  theorem x0 :
    "(drop x (drop y z)) = (drop y (drop x z))"
    apply(induction z)
    apply(simp_all add:thy_expl)
    (*
    apply(hipster_induct_schemes drop.simps thy_expl)*)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
