theory prop_42
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
  fun union :: "Nat list => Nat list => Nat list" where
  "union (Nil2) y = y"
  | "union (Cons2 z xs) y =
       (if elem z y then union xs y else Cons2 z (union xs y))"
  (*hipster equal2 elem union *)

(*hipster equal2*)
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster_cond equal2*)

lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps)

  theorem x0 :
    "(elem x y) ==> (elem x (union y z))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
