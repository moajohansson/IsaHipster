theory prop_75
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  (*hipster plus equal2 count *)
(*hipster count*)(*
lemma lemma_a []: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes count.simps)

lemma lemma_aa []: "equal2 x2 x2 = True"
by (hipster_induct_schemes count.simps)

lemma lemma_ab []: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes count.simps)*)

lemma lemma_ag [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah []: "plus (plus x2 y2) z2 = plus x2 (plus y2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aj []: "plus x2 (plus y2 x2) = plus y2 (plus x2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ak []: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_al [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_am []: "plus (plus x2 y2) x2 = plus x2 (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_an []: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ao []: "plus (plus x3 y3) (plus x3 z3) = plus (plus x3 z3) (plus x3 y3)"
by (hipster_induct_schemes Nat.exhaust)


  theorem x0 :
    "(plus (count n xs) (count n (Cons2 m (Nil2)))) = (count n (Cons2 m xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
