theory prop_49
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  (*hipster le insert2 isort equal2 elem *)

lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)
(*
hipster elem isort insert2 le equal2*)


(*hipster elem isort insert2 le equal2*)
lemma lemma_ac [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_ad [thy_expl]: "equal2 x2 Z = le x2 Z"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_ae [thy_expl]: "elem x26 (insert2 x26 y26) = True"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_af [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_ag [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_ah [thy_expl]: "elem (S x26) (insert2 x26 y26) = elem (S x26) y26"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_ai [thy_expl]: "insert2 Z (isort x3) = isort (insert2 Z x3)"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)

lemma lemma_aj [thy_expl]: "elem (S x4) (insert2 Z y4) = elem (S x4) y4"
by (hipster_induct_schemes elem.simps isort.simps insert2.simps le.simps equal2.simps)


lemma lemma_ak [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_al [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_am [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

(*hipster_cond le*)
lemma lemma_an [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ao [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ap [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_trans [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*lemma nole []: "\<not> le r s \<Longrightarrow> le s r"
by (hipster_induct_schemes le.simps Nat.exhaust)*)

lemma lemma_aq [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ar [thy_expl]: "insert2 x (insert2 y z) = insert2 y (insert2 x z)"
oops (*by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)*)

lemma lemma_as [thy_expl]: "isort (insert2 x y) = insert2 x (isort y)"
oops (*by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps)*)

lemma lemma_at [thy_expl]: "isort (isort x19) = isort x19"
oops
(*hipster_cond elem isort equal2 le*)
lemma lemma_au [thy_expl]: "elem x17 z17 \<Longrightarrow> elem x17 (insert2 y17 z17) = True"
by (hipster_induct_schemes elem.simps isort.simps equal2.simps le.simps)

lemma lemma_av [thy_expl]: "elem y35 z35 \<Longrightarrow> elem x35 (insert2 y35 z35) = elem x35 z35"
by (hipster_induct_schemes elem.simps isort.simps equal2.simps le.simps)

lemma lemma_aw [thy_expl]: "elem x21 y21 \<Longrightarrow> elem x21 (isort y21) = True"
by (hipster_induct_schemes elem.simps isort.simps equal2.simps le.simps)

(*hipster_cond le  equal2 isort elem insert2*)
lemma lemma_ax [thy_expl]: "le y26 x26 \<Longrightarrow> elem (S x26) (insert2 y26 z26) = elem (S x26) z26"
by (hipster_induct_schemes le.simps equal2.simps isort.simps elem.simps insert2.simps)

lemma missing  : "elem x (insert2 y z) = elem x (Cons2 y z)"
by (hipster_induct_schemes elem.simps isort.simps equal2.simps le.simps)

lemma unknown [thy_expl]: "elem x (isort y) = elem x y"
by (hipster_induct_schemes missing le.simps equal2.simps isort.simps elem.simps insert2.simps)


  theorem x0 :
    "(elem x (isort y)) ==> (elem x y)"
    by (hipster_induct_schemes sorted.simps isort.simps insert2.simps le.simps equal2.simps Nat.exhaust)

end
