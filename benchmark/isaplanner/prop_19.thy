theory prop_19
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
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
  (*hipster minus len drop *)
(*hipster minus*)
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

setup{* Hip_Tac_Ops.set_metis_to @{context} 600 *}
lemma woop []: "minus (minus x y) z = minus (minus x z) y"
by (hipster_induct_schemes minus.simps Nat.exhaust)
setup{* Hip_Tac_Ops.set_metis_to @{context} 400 *}

lemma unknown [thy_expl]: "minus x (minus x y) = minus y (minus y x)"
oops

lemma unknown [thy_expl]: "minus (minus x y) (minus z y) = minus (minus x z) (minus y z)"
oops

lemma unknown [thy_expl]: "minus (minus x y) (S z) =
minus (minus x z) (S y)"
oops

lemma unknown [thy_expl]: "minus (minus x y) (minus z y) =
minus (minus x y) z"
oops

lemma unknown [thy_expl]: "minus (minus x y) (minus z y) =
minus (minus x z) y"
oops

lemma unknown [thy_expl]: "minus (minus x y) (minus x z) =
minus (minus z y) (minus z x)"
oops

lemma unknown [thy_expl]: "minus (S x) (minus x y) =
minus (S y) (minus y x)"
oops
  theorem x0 :
    "(len (drop n xs)) = (minus (len xs) n)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
