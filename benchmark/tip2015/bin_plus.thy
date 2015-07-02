theory bin_plus
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus2 :: "Bin => Bin => Bin" where
"plus2 (One) y = s y"
| "plus2 (ZeroAnd z) (One) = s (ZeroAnd z)"
| "plus2 (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus2 z ys)"
| "plus2 (ZeroAnd z) (OneAnd xs) = OneAnd (plus2 z xs)"
| "plus2 (OneAnd x2) (One) = s (OneAnd x2)"
| "plus2 (OneAnd x2) (ZeroAnd zs) = OneAnd (plus2 x2 zs)"
| "plus2 (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus2 x2 ys2))"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun toNat :: "Bin => Nat" where
"toNat (One) = S Z"
| "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
| "toNat (OneAnd ys) = S (plus (toNat ys) (toNat ys))"

(*hipster s plus*)
lemma lemma_a [thy_expl]: "ZeroAnd x2 = plus2 x2 x2"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_aa [thy_expl]: "plus2 x2 One = s x2"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ab [thy_expl]: "s (plus2 x2 y2) = plus2 x2 (s y2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ac [thy_expl]: "plus2 (s x2) y2 = plus2 x2 (s y2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ad [thy_expl]: "plus2 (plus2 x1 x1) x1 = plus2 x1 (plus2 x1 x1)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ae [thy_expl]: "plus2 (s x2) (plus2 y2 z2) = plus2 (plus2 x2 y2) (s z2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_af [thy_expl]: "plus2 (s x2) (plus2 y2 z2) = plus2 (plus2 y2 z2) (s x2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ag [thy_expl]: "plus2 (plus2 x2 x2) (plus2 x2 y2) = plus2 (plus2 x2 y2) (plus2 x2 x2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ah [thy_expl]: "plus2 (plus2 x2 x2) (plus2 y2 x2) = plus2 (plus2 y2 x2) (plus2 x2 x2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ai [thy_expl]: "plus2 (plus2 x2 x2) (plus2 y2 y2) = ZeroAnd (plus2 y2 x2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_aj [thy_expl]: "plus2 x1 y1 = plus2 y1 x1"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_ak [thy_expl]: "plus2 x2 (plus2 y2 z2) = plus2 y2 (plus2 x2 z2)"
by (hipster_induct_schemes s.simps plus2.simps)

lemma lemma_al [thy_expl]: "plus2 (plus2 x2 y2) (plus2 z2 y2) = plus2 (plus2 x2 z2) (plus2 y2 y2)"
by (hipster_induct_schemes s.simps plus2.simps)

theorem x0 :
  "!! (x :: Bin) (y :: Bin) .
     (toNat (plus2 x y)) = (plus (toNat x) (toNat y))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
