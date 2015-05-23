theory prop_74
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster take minus len drop append rev *)

lemma lemma_a [thy_expl]: "minus x2 x2 = Z"
by (hipster_induct_schemes minus.simps)

lemma lemma_aa [thy_expl]: "minus x3 Z = x3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ab [thy_expl]: "minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "minus (minus x3 y3) (minus y3 x3) =
minus x3 y3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ae [thy_expl]: "minus (minus x3 y3) (S Z) = minus x3 (S y3)"
by (hipster_induct_schemes minus.simps)

lemma lemma_af [thy_expl]: "minus (minus x4 y4) x4 = Z"
by (hipster_induct_schemes minus.simps)

lemma lemma_da [thy_expl]: "drop x3 Nil2 = Nil2"
by (hipster_induct_schemes drop.simps)

lemma lemma_daa [thy_expl]: "drop (S Z) (drop x3 y3) = drop (S x3) y3"
by (hipster_induct_schemes drop.simps)

lemma lemma_ai [thy_expl]: "take x3 Nil2 = Nil2"
by (hipster_induct_schemes take.simps)

lemma lemma_aj [thy_expl]: "take x3 (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma lemma_ak [thy_expl]: "take (S x3) (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

(*hipster take drop len*)
lemma lemma_ag [thy_expl]: "drop x2 (take x2 y2) = Nil2"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_ah [thy_expl]: "drop (len x2) x2 = Nil2"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_al [thy_expl]: "take (len x2) x2 = x2"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_am [thy_expl]: "drop (len x4) (drop y4 x4) = Nil2"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_an [thy_expl]: "drop (len x3) (take y3 x3) = Nil2"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_ao [thy_expl]: "take (len x4) (drop y4 x4) = drop y4 x4"
by (hipster_induct_schemes take.simps drop.simps len.simps)

lemma lemma_ap [thy_expl]: "take (len x3) (take y3 x3) = take y3 x3"
by (hipster_induct_schemes take.simps drop.simps len.simps)


(*hipster rev append take drop len minus*)
lemma lemma_aq [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_ar [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_as [thy_expl]: "minus (len x3) y3 = len (drop y3 x3)"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_at [thy_expl]: "append (take x2 y2) (drop x2 y2) = y2"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_au [thy_expl]: "append (rev x4) (rev y4) = rev (append y4 x4)"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_av [thy_expl]: "take (len x2) (append x2 y2) = x2"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_aw [thy_expl]: "drop (len x2) (append x2 y2) = y2"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_ax [thy_expl]: "take (S Z) (append x1 x1) = take (S Z) x1"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma lemma_ay [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes rev.simps append.simps take.simps drop.simps len.simps minus.simps)

lemma unknown []: "take x (take y z) = take y (take x z)"
oops

lemma unknown []: "drop x (drop y z) = drop y (drop x z)"
oops

lemma unknown []: "minus (minus x y) z = minus (minus x z) y"
oops

lemma unknown []: "minus x (minus x y) = minus y (minus y x)"
oops

lemma lemma_applen [thy_expl]: "len (append x y) = len (append y x)"
apply(induction x)
apply(simp_all)
apply(metis thy_expl append.simps len.simps)
by (hipster_induct_schemes)

lemma lemma_revlen [thy_expl]: "len (rev x) = len x"
by (hipster_induct_schemes len.simps rev.simps)

lemma unknown []: "take (minus x y) (take x z) = take (minus x y) z"
oops

lemma unknown []: "take (minus x y) (drop y z) = drop y (take x z)"
oops

lemma unknown []: "drop (minus x y) (drop y z) = drop (minus y x) (drop x z)"
oops

lemma unknown []: "minus (minus x y) (minus z y) = minus (minus x z) (minus y z)"
oops

lemma unknown []: "minus (minus x y) (S z) = minus (minus x z) (S y)"
oops

lemma unknown []: "minus (minus x y) (minus x z) = minus (minus z y) (minus z x)"
oops

lemma unknown []: "drop (S x) (drop y z) = drop (S y) (drop x z)"
oops

lemma unknown []: "minus (S x) (minus x y) = minus (S y) (minus y x)"
oops

lemma lemma_takerev [thy_expl]: "take (len x) (rev x) = rev x"
by (hipster_induct_schemes)

lemma lemma_droprev [thy_expl]: "drop (len x) (rev x) = Nil2"
by (hipster_induct_schemes)


  theorem x0 :
    "(rev (take i xs)) = (drop (minus (len xs) i) (rev xs))"
    by (hipster_induct_schemes take.simps minus.simps rev.simps take.simps len.simps)

end
