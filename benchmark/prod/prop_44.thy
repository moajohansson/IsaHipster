theory prop_44
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (Nil2) y = Nil2"
  | "intersect (Cons2 z xs) y =
       (if elem z y then Cons2 z (intersect xs y) else intersect xs y)"

hipster equal2 elem intersect

lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster_cond equal2*)

lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ad [thy_expl]: "intersect (intersect x5 y5) y5 = intersect x5 y5"
by (hipster_induct_schemes elem.simps intersect.simps equal2.simps)

lemma lemma_ae [thy_expl]: "elem x1 z1 \<Longrightarrow> elem x1 (intersect y1 z1) = elem x1 y1"
by (hipster_induct_schemes elem.simps intersect.simps equal2.simps)

  theorem x0 :
    "(elem x y) ==> ((elem x z) ==> (elem x (intersect y z)))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
