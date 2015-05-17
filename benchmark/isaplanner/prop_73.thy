theory prop_73
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun filter2 :: "('a => bool) => 'a list => 'a list" where
  "filter2 x (Nil2) = Nil2"
  | "filter2 x (Cons2 z xs) =
       (if x z then Cons2 z (filter2 x xs) else filter2 x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster filter append rev *)

hipster filter2 rev
lemma lemma_a [thy_expl]: "prop_73.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_73.filter2.simps prop_73.rev.simps)

lemma lemma_aa [thy_expl]: "filter2 x13 (filter2 y13 z13) = filter2 y13 (filter2 x13 z13)"
by (hipster_induct_schemes prop_73.filter2.simps prop_73.rev.simps)

lemma lemma_ab [thy_expl]: "prop_73.append (prop_73.append x2 y2) z2 =
prop_73.append x2 (prop_73.append y2 z2)"
by (hipster_induct_schemes prop_73.filter2.simps prop_73.rev.simps)

lemma lemma_ac [thy_expl]: "filter2 x9 (filter2 x9 y9) = filter2 x9 y9"
by (hipster_induct_schemes prop_73.filter2.simps prop_73.rev.simps)

lemma lemma_ad [thy_expl]: "prop_73.append (filter2 x6 y6) (filter2 x6 z6) =
filter2 x6 (prop_73.append y6 z6)"
by (hipster_induct_schemes prop_73.filter2.simps prop_73.rev.simps)

lemma unknown [thy_expl]: "prop_73.rev (filter2 x y) = filter2 x (prop_73.rev y)"
oops

lemma unknown [thy_expl]: "prop_73.rev (prop_73.rev x) = x"
oops

lemma unknown [thy_expl]: "prop_73.append (prop_73.rev x) (prop_73.rev y) =
prop_73.rev (prop_73.append y x)"
oops

lemma unknown [thy_expl]: "prop_73.append (prop_73.rev x) (prop_73.rev x) =
prop_73.rev (prop_73.append x x)"
oops

lemma lemma_fa [thy_expl]: "filter2 x13 (filter2 y13 z13) = filter2 y13 (filter2 x13 z13)"
by (hipster_induct_schemes prop_73.filter2.simps)

lemma lemma_faa [thy_expl]: "filter2 x9 (filter2 x9 y9) = filter2 x9 y9"
by (hipster_induct_schemes prop_73.filter2.simps)

  theorem x0 :
    "(rev (filter2 p xs)) = (filter2 p (rev xs))"
    apply(induction xs rule: rev.induct)
    apply simp_all
    
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
