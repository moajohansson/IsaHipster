theory prop_86
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (Nil2)"
  | "ins x (Cons2 z xs) =
       (if lt x z then Cons2 x (Cons2 z xs) else Cons2 z (ins x xs))"

(*hipster lt equal2*)
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_aa [thy_expl]: "lt x2 x2 = False"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_ac [thy_expl]: "lt x2 (S x2) = True"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_ad [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_ae [thy_expl]: "lt (S x2) x2 = False"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_af [thy_expl]: "lt x2 (S Z) = equal2 x2 Z"
by (hipster_induct_schemes lt.simps equal2.simps)

lemma lemma_t [thy_expl]: "lt x y \<Longrightarrow> equal2 x y = False"
by (hipster_induct_schemes lt.simps equal2.simps)

theorem x0 : "lt x y \<Longrightarrow> ((elem x (ins y xs)) \<longleftrightarrow> (elem x xs))"
by (hipster_induct_schemes elem.simps ins.simps lt.simps Nat.exhaust list.exhaust)

end
