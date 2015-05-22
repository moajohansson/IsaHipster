theory prop_45
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun zip2 :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip2 (Nil2) y = Nil2"
  | "zip2 (Cons2 z x2) (Nil2) = Nil2"
  | "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip2 x2 x4)"
  
  hipster zip2
lemma lemma_a [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes prop_45.zip2.simps)

lemma lemma_aa [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes prop_45.zip2.simps)
  
  theorem x0 :
    "(zip2 (Cons2 x xs) (Cons2 y ys)) = (Cons2 (Pair x y) (zip2 xs ys))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
