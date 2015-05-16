theory prop_85
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => ('a * 'b) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (z, x3) (zip x2 x4)"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster zip len append rev *)
  (*hipster rev*)
lemma lemma_a [thy_expl]: "prop_85.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_85.rev.simps)

lemma lemma_aa [thy_expl]: "prop_85.append (prop_85.append x2 y2) z2 =
prop_85.append x2 (prop_85.append y2 z2)"
by (hipster_induct_schemes prop_85.rev.simps)

lemma lemma_ab [thy_expl]: "prop_85.append (prop_85.rev x5) (prop_85.rev y5) =
prop_85.rev (prop_85.append y5 x5)"
by (hipster_induct_schemes prop_85.rev.simps)

hipster len zip

lemma unknown [thy_expl]: "prop_85.rev (prop_85.rev x) = x"
oops
  theorem x0 :
    "((len xs) = (len ys)) ==>
       ((zip (rev xs) (rev ys)) = (rev (zip xs ys)))"
    apply(induction xs ys rule: zip.induct)
apply simp_all
apply(metis  zip.simps)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
