theory testind
imports Main
        "../../IsaHipster"
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

lemma lemma_a [thy_expl]: "drop x3 Nil2 = Nil2"
by (hipster_induct_simp_metis drop.simps)

lemma lemma_aa [thy_expl]: "drop (S Z) (drop x3 y3) = drop (S x3) y3"
by (hipster_induct_simp_metis drop.simps Nat.exhaust list.exhaust)

lemma lemma_ai [thy_expl]: "take x3 Nil2 = Nil2"
by (hipster_induct_simp_metis take.simps)

lemma lemma_aj [thy_expl]: "take x3 (take x3 y3) = take x3 y3"
by (hipster_induct_simp_metis take.simps Nat.exhaust list.exhaust)

lemma lemma_ak []: "take (S x3) (take x3 y3) = take x3 y3"
by (hipster_induct_simp_metis take.simps Nat.exhaust list.exhaust)

(*hipster append*)
lemma lemma_ab [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_simp_metis append.simps)

lemma lemma_ac [thy_expl]: "append (append x2 y2) z2 =
append x2 (append y2 z2)"
by (hipster_induct_simp_metis append.simps Nat.exhaust list.exhaust)


lemma lemma_abz [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_simp_metis zip2.simps)

lemma lemma_acz [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_simp_metis zip2.simps)

(*hipster zip2 append take len drop*)
lemma lemma_ad [thy_expl]: "zip2 x1 (testind.append x1 y1) = zip2 x1 x1"
by (hipster_induct_simp_metis testind.zip2.simps testind.append.simps testind.take.simps testind.len.simps testind.drop.simps testind.list.exhaust testind.Pair2.exhaust testind.Nat.exhaust)

lemma lemma_ae [thy_expl]: "zip2 (testind.append x5 y5) x5 = zip2 x5 x5"
by (hipster_induct_simp_metis testind.zip2.simps testind.append.simps testind.take.simps testind.len.simps testind.drop.simps testind.list.exhaust testind.Pair2.exhaust testind.Nat.exhaust)

lemma lemma_af [thy_expl]: "testind.take (len x2) x2 = x2"
by (hipster_induct_simp_metis testind.zip2.simps testind.append.simps testind.take.simps testind.len.simps testind.drop.simps testind.list.exhaust testind.Pair2.exhaust testind.Nat.exhaust)

lemma lemma_ag [thy_expl]: "testind.drop (len x1) (testind.append x1 y1) = y1"
by (hipster_induct_simp_metis testind.zip2.simps testind.append.simps testind.take.simps testind.len.simps testind.drop.simps testind.list.exhaust testind.Pair2.exhaust testind.Nat.exhaust)

lemma lemma_ah [thy_expl]: "testind.take (len x1) (testind.append x1 y1) = x1"
by (hipster_induct_simp_metis testind.zip2.simps testind.append.simps testind.take.simps testind.len.simps testind.drop.simps testind.list.exhaust testind.Pair2.exhaust testind.Nat.exhaust)

lemma unknown [thy_expl]: "testind.drop x (testind.drop y z) = testind.drop y (testind.drop x z)"
oops

lemma unknown [thy_expl]: "testind.take x (testind.take y z) = testind.take y (testind.take x z)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) z = zip2 y (testind.take x z)"
oops

lemma unknown [thy_expl]: "testind.drop x (testind.take x y) = testind.drop x (testind.take x z)"
oops

lemma unknown [thy_expl]: "testind.drop x (testind.take x y) = testind.drop z (testind.take z y)"
oops

lemma unknown [thy_expl]: "testind.drop x (testind.take x y) = testind.drop z (testind.take z xa)"
oops

lemma unknown [thy_expl]: "len (testind.append x y) = len (testind.append y x)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) y = zip2 y (testind.take x y)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) x = testind.drop y (testind.take y x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) x = testind.drop y (testind.take y z)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.take z xa) =
zip2 (testind.take z y) (testind.take x xa)"
oops

lemma unknown [thy_expl]: "zip2 (testind.append x y) (testind.drop z x) = zip2 x (testind.drop z x)"
oops

lemma unknown [thy_expl]: "zip2 (testind.append x y) (testind.take z x) = zip2 x (testind.take z x)"
oops

lemma unknown [thy_expl]: "zip2 (testind.drop x y) (testind.append y z) = zip2 (testind.drop x y) y"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.append y z) = zip2 y (testind.take x y)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.take x z) = zip2 y (testind.take x z)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.take z y) =
zip2 (testind.take z y) (testind.take x y)"
oops

lemma unknown [thy_expl]: "zip2 (testind.drop x y) (testind.append y y) = zip2 (testind.drop x y) y"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.take x y) = zip2 y (testind.take x y)"
oops

lemma unknown [thy_expl]: "zip2 (testind.take x y) (testind.append y y) = zip2 y (testind.take x y)"
oops

lemma unknown [thy_expl]: "testind.append (testind.take x y) (testind.drop x y) = y"
oops

lemma unknown [thy_expl]: "zip2 (testind.append x x) (testind.drop y x) = zip2 x (testind.drop y x)"
oops

lemma unknown [thy_expl]: "zip2 (testind.append x x) (testind.take y x) = zip2 x (testind.take y x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.drop y x) = testind.drop y (testind.take y x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.drop y x) = testind.drop z (testind.take z x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.take y x) = testind.drop y (testind.take y x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.take y x) = testind.drop z (testind.take z x)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.drop y x) = testind.drop y (testind.take y z)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.drop y x) = testind.drop z (testind.take z xa)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.take y x) = testind.drop y (testind.take y z)"
oops

lemma unknown [thy_expl]: "testind.drop (len x) (testind.take y x) = testind.drop z (testind.take z xa)"
oops

lemma unknown [thy_expl]: "testind.take (len x) (testind.drop y x) = testind.drop y x"
oops

lemma unknown [thy_expl]: "testind.take (len x) (testind.take y x) = testind.take y x"
oops

theorem t: "len a = len b \<Longrightarrow> append (zip2 a b) (zip2 c d) = zip2 (append a c) (append b d)"
       apply(induction d arbitrary: a b c)
       apply simp_all
       sledgehammer
       by (hipster_induct_simp_metis zip2.simps len.simps take.simps drop.simps append.simps Nat.exhaust list.exhaust)


  theorem x0 :
    "(zip2 (append xs ys) zs) =
       (append (zip2 xs (take (len xs) zs)) (zip2 ys (drop (len xs) zs)))"
       apply(induction zs arbitrary: ys xs)
       apply simp_all

apply (metis lemma_a lemma_acz lemma_ai testind.append.simps(1) zip2.simps(1))
sledgehammer
       by (hipster_induct_simp_metis zip2.simps len.simps take.simps drop.simps append.simps Nat.exhaust list.exhaust)

end
