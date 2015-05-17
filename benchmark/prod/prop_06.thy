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

hipster append rev length
lemma lemma_a [thy_expl]: "prop_06.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_06.append.simps prop_06.rev.simps prop_06.length.simps)

lemma lemma_aa [thy_expl]: "prop_06.append (prop_06.append x2 y2) z2 =
prop_06.append x2 (prop_06.append y2 z2)"
by (hipster_induct_schemes prop_06.append.simps prop_06.rev.simps prop_06.length.simps)

lemma lemma_ab [thy_expl]: "prop_06.append (prop_06.rev x5) (prop_06.rev y5) =
prop_06.rev (prop_06.append y5 x5)"
by (hipster_induct_schemes prop_06.append.simps prop_06.rev.simps prop_06.length.simps)

lemma lemma_ac [thy_expl]: "prop_06.rev (prop_06.rev x5) = x5"
by (hipster_induct_schemes prop_06.append.simps prop_06.rev.simps prop_06.length.simps)

lemma unknown [thy_expl]: "prop_06.length (prop_06.append x y) = prop_06.length (prop_06.append y x)"
oops

lemma unknown [thy_expl]: "prop_06.length (prop_06.rev x) = prop_06.length x"
oops

lemma lemma_ag [thy_expl]: "prop_06.plus x2 Z = x2"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_ah [thy_expl]: "prop_06.plus (prop_06.plus x2 y2) z2 = prop_06.plus x2 (prop_06.plus y2 z2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_ai [thy_expl]: "prop_06.plus x2 (S y2) = S (prop_06.plus x2 y2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_aj [thy_expl]: "prop_06.plus x2 (prop_06.plus y2 x2) = prop_06.plus y2 (prop_06.plus x2 x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_ak [thy_expl]: "prop_06.plus x2 (prop_06.plus y2 y2) = prop_06.plus y2 (prop_06.plus y2 x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_al [thy_expl]: "prop_06.plus x2 (S y2) = S (prop_06.plus y2 x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_am [thy_expl]: "prop_06.plus (prop_06.plus x2 y2) x2 = prop_06.plus x2 (prop_06.plus x2 y2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_an [thy_expl]: "prop_06.plus (S x2) y2 = S (prop_06.plus y2 x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_ao [thy_expl]: "prop_06.plus (prop_06.plus x3 y3) (prop_06.plus x3 z3) =
prop_06.plus (prop_06.plus x3 z3) (prop_06.plus x3 y3)"
by (hipster_induct_schemes )

lemma lemma_ap [thy_expl]: "prop_06.plus (prop_06.plus x2 y2) (prop_06.plus z2 y2) =
prop_06.plus (prop_06.plus x2 z2) (prop_06.plus y2 y2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_aq [thy_expl]: "prop_06.plus (prop_06.plus x3 y3) (prop_06.plus z3 z3) =
prop_06.plus (prop_06.plus x3 z3) (prop_06.plus z3 y3)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_az [thy_expl]: "prop_06.plus (S x2) (prop_06.plus y2 z2) =
prop_06.plus (prop_06.plus y2 z2) (S x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_ba [thy_expl]: "prop_06.plus (prop_06.plus x2 x2) (prop_06.plus y2 y2) =
prop_06.plus (prop_06.plus x2 y2) (prop_06.plus x2 y2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_bb [thy_expl]: "prop_06.plus (prop_06.plus x2 x2) (S y2) =
prop_06.plus (prop_06.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_bc [thy_expl]: "prop_06.plus (prop_06.plus x2 x2) (prop_06.plus y2 y2) =
prop_06.plus (prop_06.plus y2 x2) (prop_06.plus y2 x2)"
by (hipster_induct_schemes prop_06.plus.simps)
(*
lemma lemma_bd [thy_expl]: "prop_06.plus (S x2) (prop_06.plus x2 y2) =
prop_06.plus (prop_06.plus x2 y2) (S x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_be [thy_expl]: "prop_06.plus (S x2) (prop_06.plus y2 x2) =
prop_06.plus (prop_06.plus y2 x2) (S x2)"
by (hipster_induct_schemes prop_06.plus.simps)*)

lemma lemma_bf [thy_expl]: "prop_06.plus (S x2) (S y2) = prop_06.plus (S y2) (S x2)"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_bg [thy_expl]: "prop_06.plus x2 y2 = prop_06.plus y2 x2"
by (hipster_induct_schemes prop_06.plus.simps)

lemma lemma_bh [thy_expl]: "prop_06.plus x2 (prop_06.plus y2 z2) = prop_06.plus y2 (prop_06.plus x2 z2)"
by (hipster_induct_schemes prop_06.plus.simps)

hipster length append
(*
lemma ax: "prop_06.length (prop_06.append (Cons2 ya xs) y) = S (prop_06.length (prop_06.append xs y))"
by (metis length.simps(2) prop_06.append.simps(2))

lemma ax2[]: "prop_06.length (prop_06.append y (Cons2 ya xs)) = S (prop_06.length (prop_06.append y xs))"
by(hipster_induct_schemes)*)

  theorem x0 :
    "(length (rev (append x y))) = (plus (length x) (length y))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
