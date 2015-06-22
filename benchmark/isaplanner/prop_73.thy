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

(*hipster filter2 rev*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes filter2.simps rev.simps)

lemma lemma_aa []: "filter2 x13 (filter2 y13 z13) = filter2 y13 (filter2 x13 z13)"
by (hipster_induct_schemes filter2.simps rev.simps)

lemma lemma_ab [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes filter2.simps rev.simps)

lemma lemma_ac []: "filter2 x9 (filter2 x9 y9) = filter2 x9 y9"
by (hipster_induct_schemes filter2.simps rev.simps)

lemma lemma_ad [thy_expl]: "append (filter2 x6 y6) (filter2 x6 z6) = filter2 x6 (append y6 z6)"
by (hipster_induct_schemes filter2.simps rev.simps)

(*hipster rev append filter2*)
lemma lemma_ae [thy_expl]: "append (rev x4) (rev y4) = rev (append y4 x4)"
by (hipster_induct_schemes rev.simps append.simps filter2.simps)

lemma lemma_af [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes rev.simps append.simps filter2.simps)

lemma ss: "f x \<Longrightarrow> filter2 f (Cons2 x y) = Cons2 x (filter2 f y)"
by simp

lemma sst: "\<not> f x \<Longrightarrow> filter2 f (Cons2 x y) = (filter2 f y)"
by simp
setup {* Hip_Tac_Ops.set_metis_to @{context} 2000 *}

lemma unknown []: "rev (filter2 x y) = filter2 x (rev y)"
    by (hipster_induct_schemes rev.simps append.simps filter2.simps)

apply(induction y)
apply(simp_all)
by (metis rev.simps append.simps filter2.simps thy_expl) (*lemma_ad lemma_a lemma_ab lemma_ac lemma_ae lemma_af)*)

setup {* Hip_Tac_Ops.set_metis_to @{context} 2000 *}
  theorem x0 :
    "(rev (filter2 p xs)) = (filter2 p (rev xs))"
    by (hipster_induct_schemes rev.simps append.simps filter2.simps)

end

