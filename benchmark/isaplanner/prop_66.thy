theory prop_66
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun filter2 :: "('a => bool) => 'a list => 'a list" where
  "filter2 x (Nil2) = Nil2"
  | "filter2 x (Cons2 z xs) =
       (if x z then Cons2 z (filter2 x xs) else filter2 x xs)"
  (*hipster len le filter *)
hipster len filter2
lemma lemma_a []: "filter2 x13 (filter2 y13 z13) = filter2 y13 (filter2 x13 z13)"
by (hipster_induct_schemes len.simps filter2.simps)

lemma lemma_aa []: "filter2 x9 (filter2 x9 y9) = filter2 x9 y9"
by (hipster_induct_schemes len.simps filter2.simps)

(*hipster le*)
lemma lemma_ab []: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ac []: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad []: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

(*hipster_cond le len*)
lemma lemma_ae [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes)

lemma lemma_af []: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ag []: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ah []: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(* Trivial
lemma lemma_ai [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x (S y) = True"
lemma lemma_aj [thy_expl]: "le z x \<and> le y z \<Longrightarrow> le (S x) y = False"
lemma lemma_ak [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le (S x) (S y) = True"
*)

  theorem x0 :
    "le (len (filter2 q xs)) (len xs)"
    by (hipster_induct_schemes)

end
