theory prop_57
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
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster take minus drop *)
lemma lemma_a [thy_expl]: "minus x2 x2 = Z"
by (hipster_induct_schemes minus.simps)

lemma lemma_aa [thy_expl]: "minus x3 Z = x3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ab [thy_expl]: "minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "minus (minus x3 y3) (minus y3 x3) = minus x3 y3"
by (hipster_induct_schemes minus.simps)

lemma lemma_ae [thy_expl]: "minus (minus x3 y3) (S Z) = minus x3 (S y3)"
by (hipster_induct_schemes minus.simps)

lemma lemma_af [thy_expl]: "minus (minus x4 y4) x4 = Z"
by (hipster_induct_schemes minus.simps)

lemma lemma_ag [thy_expl]: "drop x3 Nil2 = Nil2"
by (hipster_induct_schemes drop.simps)

lemma lemma_ah [thy_expl]: "drop (S Z) (drop x3 y3) = drop (S x3) y3"
by (hipster_induct_schemes drop.simps)

lemma unknown [thy_expl]: "drop x (drop y z) = drop y (drop x z)"
oops

lemma unknown [thy_expl]: "drop (S x) (drop y z) = drop (S y) (drop x z)"
oops

(*hipster take*)
lemma lemma_ai [thy_expl]: "take x3 Nil2 = Nil2"
by (hipster_induct_schemes take.simps)

lemma lemma_aj [thy_expl]: "take x3 (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma lemma_ak [thy_expl]: "take (S x3) (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma unknown [thy_expl]: "take x (take y z) = take y (take x z)"
oops

  theorem x0 :
    "(drop n (take m xs)) = (take (minus m n) (drop n xs))"
    by (hipster_induct_schemes take.simps drop.simps minus.simps Nat.exhaust list.exhaust)

end

