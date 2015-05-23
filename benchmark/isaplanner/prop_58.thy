theory prop_58
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip2 :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip2 (Nil2) y = Nil2"
  | "zip2 (Cons2 z x2) (Nil2) = Nil2"
  | "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip2 x2 x4)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster zip drop *)
lemma lemma_a [thy_expl]: "prop_58.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_58.drop.simps)

lemma lemma_aa [thy_expl]: "prop_58.drop (S Z) (prop_58.drop x3 y3) = prop_58.drop (S x3) y3"
by (hipster_induct_schemes prop_58.drop.simps)

(*hipster zip2*)
lemma lemma_ab [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes prop_58.zip2.simps)

lemma lemma_ac [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes prop_58.zip2.simps)

(*hipster zip2 drop*)

  theorem x0 :
    "(drop n (zip2 xs ys)) = (zip2 (drop n xs) (drop n ys))"
    by (hipster_induct_schemes drop.simps zip2.simps  Nat.exhaust)
(*
    apply(induction xs ys arbitrary: n rule: zip2.induct)
    apply(simp_all)
    apply(metis drop.simps thy_expl zip2.simps)
    apply(metis drop.simps thy_expl zip2.simps)

    apply(metis drop.simps thy_expl zip2.simps  Nat.exhaust)
by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
