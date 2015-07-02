theory prop_47
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a Tree = Leaf | Node "'a Tree" "'a" "'a Tree"
  datatype Nat = Z | S "Nat"
  fun mirror :: "'a Tree => 'a Tree" where
  "mirror (Leaf) = Leaf"
  | "mirror (Node l y r) = Node (mirror r) y (mirror l)"
  fun max2 :: "Nat => Nat => Nat" where
  "max2 (Z) y = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
  | "height (Node l y r) = S (max2 (height l) (height r))"
  (*hipster mirror max2 height *)

(*hipster mirror
lemma lemma_ta []: "mirror (mirror x2) = x2"
by (hipster_induct_schemes mirror.simps)*)

lemma lemma_a [thy_expl]: "max2 x x = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_aa [thy_expl]: "max2 x Z = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ab [thy_expl]: "max2 x (max2 x y) = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ac [thy_expl]: "max2 x (max2 y x) = max2 y x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ad [thy_expl]: "max2 (max2 x y) x = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ae [thy_expl]: "max2 (S x) y = max2 y (S x)"
by (hipster_induct_schemes max2.simps)

lemma lemma_af [thy_expl]: "max2 x y = max2 y x"
by (hipster_induct_schemes max2.simps)


(*hipster height*)
  theorem x0 :
    "(height (mirror b)) = (height b)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
