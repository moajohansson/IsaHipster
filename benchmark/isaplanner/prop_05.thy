theory prop_05
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  (*hipster equal2 count *)
  hipster equal2
lemma lemma_a [thy_expl]: "equal2 x x = True"
apply (induction x)
apply simp
by simp

lemma lemma_aa [thy_expl]: "equal2 Z x = equal2 x Z"
apply (induction x)
apply simp
by simp

lemma lemma_ab [thy_expl]: "equal2 (S x) y = equal2 y (S x)"
apply (induction y)
(*apply (metis equal2.elims(2) equal2.simps(1))*)
sledgehammer
apply simp
apply simp
sledgehammer
oops

lemma lemma_ac [thy_expl]: "equal2 x (S x) = False"
apply (induction x)
apply simp
by simp
(*
lemma lemma_ad [thy_expl]: "equal2 (S x) (S y) = equal2 y x"
apply (induction x)
apply (metis equal2.elims(2) equal2.simps(1) equal2.simps(3))
apply (metis Nat.distinct(1) Nat.inject equal2.elims(2) equal2.elims(3) equal2.simps(2) equal2.simps(3) equal2.simps(4))
apply simp
by simp
lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes prop_05.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_05.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_05.equal2.simps)
  theorem x0 :
    "(n = x) ==> ((S (count n xs)) = (count n (Cons2 x xs)))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
