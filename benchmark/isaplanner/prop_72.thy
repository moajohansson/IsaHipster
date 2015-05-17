theory prop_72
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

lemma lemma_da [thy_expl]: "prop_72.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_72.drop.simps)

lemma lemma_daa [thy_expl]: "prop_72.drop (S Z) (prop_72.drop x3 y3) = prop_72.drop (S x3) y3"
by (hipster_induct_schemes prop_72.drop.simps)

lemma lemma_a [thy_expl]: "prop_72.minus x2 x2 = Z"
by (hipster_induct_schemes prop_72.minus.simps)

lemma lemma_aa [thy_expl]: "prop_72.minus x3 Z = x3"
by (hipster_induct_schemes prop_72.minus.simps)

lemma lemma_ab [thy_expl]: "prop_72.minus x2 (S x2) = Z"
by (hipster_induct_schemes)

lemma lemma_ac [thy_expl]: "prop_72.minus (S x2) x2 = S Z"
by (hipster_induct_schemes)

lemma lemma_ad [thy_expl]: "prop_72.minus (prop_72.minus x3 y3) (prop_72.minus y3 x3) =
prop_72.minus x3 y3"
by (hipster_induct_schemes prop_72.minus.simps)

lemma lemma_ae [thy_expl]: "prop_72.minus (prop_72.minus x3 y3) (S Z) = prop_72.minus x3 (S y3)"
by (hipster_induct_schemes prop_72.minus.simps)

lemma lemma_af [thy_expl]: "prop_72.minus (prop_72.minus x4 y4) x4 = Z"
by (hipster_induct_schemes prop_72.minus.simps)


  theorem x0 :
    "(rev (drop i xs)) = (take (minus (len xs) i) (rev xs))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
