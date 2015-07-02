theory prop_83
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip2 :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip2 (Nil2) y = Nil2"
  | "zip2 (Cons2 z x2) (Nil2) = Nil2"
  | "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip2 x2 x4)"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
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
  (*hipster zip2 take len drop append *)

lemma lemma_a [thy_expl]: "prop_83.drop x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_83.drop.simps)

lemma lemma_aa [thy_expl]: "prop_83.drop (S Z) (prop_83.drop x3 y3) = prop_83.drop (S x3) y3"
by (hipster_induct_schemes prop_83.drop.simps)

lemma lemma_ai [thy_expl]: "prop_83.take x3 Nil2 = Nil2"
by (hipster_induct_schemes prop_83.take.simps)

lemma lemma_aj [thy_expl]: "prop_83.take x3 (prop_83.take x3 y3) = prop_83.take x3 y3"
by (hipster_induct_schemes prop_83.take.simps)

lemma lemma_ak [thy_expl]: "prop_83.take (S x3) (prop_83.take x3 y3) = prop_83.take x3 y3"
by (hipster_induct_schemes prop_83.take.simps)

(*hipster append*)
lemma lemma_ab [thy_expl]: "prop_83.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_83.append.simps)

lemma lemma_ac [thy_expl]: "prop_83.append (prop_83.append x2 y2) z2 =
prop_83.append x2 (prop_83.append y2 z2)"
by (hipster_induct_schemes prop_83.append.simps)


lemma lemma_abz [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes zip2.simps)

lemma lemma_acz [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes zip2.simps)

  theorem x0 :
    "(zip2 (append xs ys) zs) =
       (append (zip2 xs (take (len xs) zs)) (zip2 ys (drop (len xs) zs)))"
       by (hipster_induct_schemes zip2.simps len.simps take.simps drop.simps append.simps)

end
