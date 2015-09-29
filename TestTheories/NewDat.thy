theory NewDat
imports Main
        "../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
(*datatype_compat list
datatype_compat Nat*)

  fun zip2 :: "'a list => 'b list => ('a * 'b) list" where
  "zip2 (Nil2) y = Nil2"
  | "zip2 (Cons2 z x2) (Nil2) = Nil2"
  | "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (z, x3) (zip2 x2 x4)"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster zip2 len append rev *)
  (*hipster rev*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes rev.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes rev.simps)

lemma lemma_ab [thy_expl]: "append (rev x5) (rev y5) = rev (append y5 x5)"
by (hipster_induct_schemes rev.simps)

(*hipster len zip2*)
lemma lemma_ac [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes len.simps zip2.simps)

lemma lemma_ad [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes len.simps zip2.simps)


(*hipster rev zip2*)
lemma lemma_ae [thy_expl]: "zip2 x2 (append x2 y2) = zip2 x2 x2"
by (hipster_induct_schemes rev.simps zip2.simps)

lemma lemma_af [thy_expl]: "zip2 (append x1 y1) x1 = zip2 x1 x1"
by (hipster_induct_schemes rev.simps zip2.simps)


(*hipster zip2 append*)
lemma lemma_ah [thy_expl]: "zip2 (append x4 x4) (Cons2 y4 Nil2) = zip2 x4 (Cons2 y4 Nil2)"
by (hipster_induct_schemes zip2.simps append.simps)

lemma lemma_ai [thy_expl]: "zip2 (Cons2 x1 Nil2) (append y1 y1) = zip2 (Cons2 x1 Nil2) y1"
by (hipster_induct_schemes zip2.simps append.simps)

(*hipster len rev append*)
lemma lemma_aj [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes len.simps rev.simps append.simps)

end
