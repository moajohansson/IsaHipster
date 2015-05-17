theory prop_20
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  (*hipster len le insort sort *)
  (*hipster insort*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes prop_20.insort.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes prop_20.insort.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes prop_20.insort.simps)

lemma unknown [thy_expl]: "prop_20.insort x (prop_20.insort y z) =
prop_20.insort y (prop_20.insort x z)"
oops

lemma unknown [thy_expl]: "prop_20.insort Z (prop_20.insort x y) =
prop_20.insort x (prop_20.insort Z y)"
oops

(*hipster len sort*)
lemma lemma_ac [thy_expl]: "prop_20.insort Z (prop_20.sort x2) = prop_20.sort (prop_20.insort Z x2)"
by (hipster_induct_schemes prop_20.len.simps prop_20.sort.simps)

lemma unknown [thy_expl]: "prop_20.insort x (prop_20.insort y z) =
prop_20.insort y (prop_20.insort x z)"
oops

lemma unknown [thy_expl]: "prop_20.sort (prop_20.insort x y) = prop_20.insort x (prop_20.sort y)"
oops

lemma unknown [thy_expl]: "prop_20.sort (prop_20.sort x) = prop_20.sort x"
oops


  theorem x0 :
    "(len (sort xs)) = (len xs)"
    by (hipster_induct_schemes lemma_aa lemma_ab lemma_ac sort.simps len.simps insort.simps list.exhaust)
    apply(induction xs rule: sort.induct)
    apply(simp_all add: lemma_aa lemma_ab lemma_ac)
    by (hipster_induct_schemes lemma_aa lemma_ab lemma_ac)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
