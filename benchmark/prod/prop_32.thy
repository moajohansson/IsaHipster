theory prop_32
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
  | "rotate (S z) (Nil2) = Nil2"
  | "rotate (S z) (Cons2 x2 x3) =
       rotate z (append x3 (Cons2 x2 (Nil2)))"
  (*hipster length append rotate *)
hipster length append rotate
lemma lemma_a [thy_expl]: "prop_32.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma lemma_aa [thy_expl]: "prop_32.rotate x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma lemma_ab [thy_expl]: "prop_32.append (prop_32.append x2 y2) z2 =
prop_32.append x2 (prop_32.append y2 z2)"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma lemma_ac [thy_expl]: "prop_32.rotate x2 (Cons2 y2 Nil2) = Cons2 y2 Nil2"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma lemma_ad [thy_expl]: "prop_32.append (prop_32.rotate x3 y3) (prop_32.rotate x3 y3) =
prop_32.rotate x3 (prop_32.append y3 y3)"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma lemma_ae [thy_expl]: "prop_32.rotate (S Z) (prop_32.rotate x3 y3) = prop_32.rotate (S x3) y3"
by (hipster_induct_schemes prop_32.length.simps prop_32.append.simps prop_32.rotate.simps)

lemma unknown [thy_expl]: "prop_32.rotate x (prop_32.rotate y z) =
prop_32.rotate y (prop_32.rotate x z)"
oops

lemma unknown [thy_expl]: "prop_32.length (prop_32.append x y) = prop_32.length (prop_32.append y x)"
oops

lemma unknown [thy_expl]: "prop_32.length (prop_32.rotate x y) = prop_32.length y"
oops

lemma unknown [thy_expl]: "prop_32.rotate (prop_32.length x) x = x"
oops

lemma unknown [thy_expl]: "prop_32.rotate (S x) (prop_32.rotate y z) =
prop_32.rotate (S y) (prop_32.rotate x z)"
oops

lemma unknown [thy_expl]: "prop_32.rotate (prop_32.length x) (prop_32.append x y) = prop_32.append y x"
oops

lemma unknown [thy_expl]: "prop_32.rotate (prop_32.length x) (prop_32.rotate y x) = prop_32.rotate y x"
oops

lemma unknown [thy_expl]: "prop_32.rotate (prop_32.length x) (prop_32.append x x) = prop_32.append x x"
oops

  theorem x0 :
    "(rotate (length x) x) = x"
    by hipster_induct_schemes
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
