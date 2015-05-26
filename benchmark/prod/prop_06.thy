theory prop_06
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster plus length append rev *)

(*hipster append rev length*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps rev.simps length.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps rev.simps length.simps)

lemma lemma_ab [thy_expl]: "append (rev x5) (rev y5) = rev (append y5 x5)"
by (hipster_induct_schemes append.simps rev.simps length.simps)

lemma lemma_ac [thy_expl]: "rev (rev x5) = x5"
by (hipster_induct_schemes append.simps rev.simps length.simps)

lemma unknown []: "length (append x y) = length (append y x)"
oops

lemma unknown []: "length (rev x) = length x"
oops

lemma lemma_ag [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) z2 = plus x2 (plus y2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aj [thy_expl]: "plus x2 (plus y2 x2) = plus y2 (plus x2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ak [thy_expl]: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_al [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_am [thy_expl]: "plus (plus x2 y2) x2 = plus x2 (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_an [thy_expl]: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ao [thy_expl]: "plus (plus x3 y3) (plus x3 z3) = plus (plus x3 z3) (plus x3 y3)"
by (hipster_induct_schemes plus.simps Nat.exhaust)

lemma lemma_ap [thy_expl]: "plus (plus x2 y2) (plus z2 y2) = plus (plus x2 z2) (plus y2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aq [thy_expl]: "plus (plus x3 y3) (plus z3 z3) = plus (plus x3 z3) (plus z3 y3)"
by (hipster_induct_schemes plus.simps)

lemma lemma_az [thy_expl]: "plus (S x2) (plus y2 z2) = plus (plus y2 z2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ba [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus x2 y2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bb [thy_expl]: "plus (plus x2 x2) (S y2) = plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bc [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus y2 x2) (plus y2 x2)"
by (hipster_induct_schemes plus.simps)
(*
lemma lemma_bd [thy_expl]: "plus (S x2) (plus x2 y2) =
plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_be [thy_expl]: "plus (S x2) (plus y2 x2) =
plus (plus y2 x2) (S x2)"
by (hipster_induct_schemes plus.simps)*)

lemma lemma_bf [thy_expl]: "plus (S x2) (S y2) = plus (S y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bg [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_bh [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

(*hipster length append rev*)
(*
lemma ax: "length (append (Cons2 ya xs) y) = S (length (append xs y))"
by (metis length.simps(2) append.simps(2))

lemma ax2[]: "length (append y (Cons2 ya xs)) = S (length (append y xs))"
by(hipster_induct_schemes)*)

(*hipster length plus append rev*)
lemma lemma_ad [thy_expl]: "plus (length x2) (length y2) = length (append x2 y2)"
by (hipster_induct_schemes length.simps plus.simps append.simps rev.simps)

lemma lemma_ae [thy_expl]: "plus (length x1) (length y1) = length (append y1 x1)"
by (hipster_induct_schemes length.simps plus.simps append.simps rev.simps)

lemma lemma_af [thy_expl]: "length (rev x3) = length x3"
by (hipster_induct_schemes length.simps plus.simps append.simps rev.simps)

  theorem x0 :
    "(length (rev (append x y))) = (plus (length x) (length y))"
    by (hipster_induct_schemes rev.simps append.simps plus.simps length.simps list.exhaust)

end
