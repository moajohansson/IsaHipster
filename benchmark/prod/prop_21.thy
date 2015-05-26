theory prop_21
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


lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes  append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps)

lemma lemma_ab [thy_expl]: "rotate x1 Nil2 = Nil2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ac [thy_expl]: "rotate x2 (Cons2 y2 Nil2) = Cons2 y2 Nil2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ad [thy_expl]: "append (rotate x3 y3) (rotate x3 y3) = rotate x3 (append y3 y3)"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ae [thy_expl]: "rotate (S Z) (rotate x2 y2) = rotate (S x2) y2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma unknown []: "rotate x (rotate y z) = rotate y (rotate x z)"
oops

lemma unknown' []: "rotate (S x) (rotate y z) = rotate (S y) (rotate x z)"
oops

  theorem x0 :
    "(rotate (length x) (append x y)) = (append y x)"
    by (hipster_induct_schemes rotate.simps append.simps length.simps Nat.exhaust list.exhaust)

end
