theory prop_03
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
  (*hipster plus length append *)

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
by (hipster_induct_schemes )

lemma lemma_ap [thy_expl]: "plus (plus x2 y2) (plus z2 y2) = plus (plus x2 z2) (plus y2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aq [thy_expl]: "plus (plus x3 y3) (plus z3 z3) = plus (plus x3 z3) (plus z3 y3)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ar [thy_expl]: "plus (plus x2 y2) (S z2) = plus (plus x2 z2) (S y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ay [thy_expl]: "plus (S x2) (plus y2 z2) =
plus (plus y2 x2) (S z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_az [thy_expl]: "plus (S x2) (plus y2 z2) = plus (plus y2 z2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ba [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus x2 y2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bb [thy_expl]: "plus (plus x2 x2) (S y2) = plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bc [thy_expl]: "plus (plus x2 x2) (plus y2 y2) = plus (plus y2 x2) (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bd [thy_expl]: "plus (S x2) (plus x2 y2) = plus (plus x2 y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_be [thy_expl]: "plus (S x2) (plus y2 x2) = plus (plus y2 x2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bf [thy_expl]: "plus (S x2) (S y2) = plus (S y2) (S x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_bg [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_bh [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

(*hipster length append*)
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes length.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes length.simps append.simps)

lemma unknown' []: "length (append x y) = length (append y x)"
oops

(*hipster length append plus
lemma lemma_ab [thy_expl]: "plus (length x2) (length y2) = length (append x2 y2)"
by (hipster_induct_schemes length.simps append.simps plus.simps)

lemma lemma_ac [thy_expl]: "plus (length x4) (length y4) = length (append y4 x4)"
by (hipster_induct_schemes length.simps append.simps plus.simps)*)

(*
lemma xx[thy_expl]: "len (append xs (Cons2 y ys)) = S (len (prop_85.append xs ys))"
sorry*)
  theorem x0 [thy_expl]:
    "(length (append x y)) = (plus (length y) (length x))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

lemma unknown [thy_expl]: "length (append x y) = length (append y x)"
by (metis thy_expl)

end
