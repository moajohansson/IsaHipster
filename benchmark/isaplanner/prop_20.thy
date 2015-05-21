theory prop_20
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (y) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  (*hipster len le insort sort *)
  (*hipster insort*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes prop_20.insort.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes prop_20.insort.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes prop_20.insort.simps)

lemma unknown [thy_expl]: "prop_20.insort x (prop_20.insort y z) =
prop_20.insort y (prop_20.insort x z)"
oops

lemma unknown [thy_expl]: "prop_20.insort Z (prop_20.insort x y) =
prop_20.insort x (prop_20.insort Z y)"
oops

(*hipster len sort*)
lemma lemma_ac [thy_expl]: "prop_20.insort Z (prop_20.sort x2) = prop_20.sort (prop_20.insort Z x2)"
by (hipster_induct_schemes prop_20.len.simps prop_20.sort.simps)

lemma unknown [thy_expl]: "prop_20.insort x (prop_20.insort y z) =
prop_20.insort y (prop_20.insort x z)"
oops

lemma unknown [thy_expl]: "prop_20.sort (prop_20.insort x y) = prop_20.insort x (prop_20.sort y)"
oops

lemma unknown [thy_expl]: "prop_20.sort (prop_20.sort x) = prop_20.sort x"
oops

(*hipster_cond le*)
lemma le_a : "(le (S Z) (S x) = True)"
by (tactic {* Tactic_Data.routine_tac @{context}*})

lemma le_aa [thy_expl]: "(le x y \<Longrightarrow> le x (S y))"
by (hipster_induct_schemes)

lemma le_ab [thy_expl]: "(le y x \<Longrightarrow> le (S x) y = False)"
by (hipster_induct_schemes)

lemma le_ac: "(le x y \<Longrightarrow> le (S x) (S y) = True)"
by (tactic {* Tactic_Data.routine_tac @{context}*})

lemma le_ad [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)
(*
lemma le_ae: "(\<lbrakk> le x z; le z y \<rbrakk> \<Longrightarrow> le x y)"
oops

lemma le_af: "(le z y \<and> le x z \<Longrightarrow> le x (S y) = True)"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_ag: "(le z x \<and> le y z \<Longrightarrow> le (S x) y = False)"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma le_ah: "(le z y \<and> le x z \<Longrightarrow> le (S x) (S y) = True)"
by (hipster_induct_schemes le.simps Nat.exhaust)
*)
(*
lemma le_ai: "(le x y \<and> le x z \<Longrightarrow> le x (S Z) = True)"
by (hipster_induct_schemes le.simps Nat.exhaust)*)

lemma notfound01 [thy_expl]: "len (insort t xs) = S (len xs)"
by hipster_induct_schemes

  theorem x0 :                      
    "(len (sort xs)) = (len xs)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
