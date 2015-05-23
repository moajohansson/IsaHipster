theory prop_82
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip x2 x4)"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  (*hipster zip take *)
lemma lemma_ai [thy_expl]: "prop_82.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_82.take.simps)

lemma lemma_aj [thy_expl]: "prop_82.take x3 (prop_82.take x3 y3) = prop_82.take x3 y3"
by (hipster_induct_schemes prop_82.take.simps)

lemma lemma_ak [thy_expl]: "prop_82.take (S x3) (prop_82.take x3 y3) = prop_82.take x3 y3"
by (hipster_induct_schemes prop_82.take.simps)

lemma lemma_ab [thy_expl]: "zip Nil2 x1 = zip x1 Nil2"
by (hipster_induct_schemes zip.simps)

lemma lemma_ac [thy_expl]: "zip Nil2 x1 = zip y1 Nil2"
by (hipster_induct_schemes zip.simps)

  theorem x0 :
    "(take n (zip xs ys)) = (zip (take n xs) (take n ys))"
    apply(induction xs ys arbitrary: n rule: zip.induct)
    apply(simp_all)
    apply(metis thy_expl zip.simps take.simps)
    apply(metis thy_expl zip.simps take.simps)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
