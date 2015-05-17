theory prop_77
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
  | "sorted (Cons2 y (Nil2)) = True"
  | "sorted (Cons2 y (Cons2 y2 ys)) =
       (if le y y2 then sorted (Cons2 y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  (*hipster le sorted insort *)
(*hipster insort le*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes prop_77.insort.simps prop_77.le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes prop_77.insort.simps prop_77.le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes prop_77.insort.simps prop_77.le.simps)

lemma unknown [thy_expl]: "prop_77.insort x (prop_77.insort y z) =
prop_77.insort y (prop_77.insort x z)"
oops

lemma unknown [thy_expl]: "prop_77.insort Z (prop_77.insort x y) =
prop_77.insort x (prop_77.insort Z y)"
oops
  theorem x0 :
    "(sorted xs) ==> (sorted (insort x xs))"
    apply(induction xs rule:insort.induct)
    apply simp_all
    apply(metis insort.elims)
    (*apply(metis insort.simps le.simps)*)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
