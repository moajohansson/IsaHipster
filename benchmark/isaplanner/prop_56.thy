theory prop_56
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster plus drop *)

(*hipster drop*)
lemma lemma_a [thy_expl]: "prop_56.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_56.drop.simps)

lemma lemma_aa [thy_expl]: "prop_56.drop (S Z) (prop_56.drop x3 y3) = prop_56.drop (S x3) y3"
by (hipster_induct_schemes prop_56.drop.simps)

lemma unknown [thy_expl]: "prop_56.drop x (prop_56.drop y z) = prop_56.drop y (prop_56.drop x z)"
oops

lemma unknown [thy_expl]: "prop_56.drop (S x) (prop_56.drop y z) =
prop_56.drop (S y) (prop_56.drop x z)"
oops

  theorem x0 :
    "(drop n (drop m xs)) = (drop (plus n m) xs)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
