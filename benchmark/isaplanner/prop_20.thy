theory prop_20
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "Nat list => Nat" where
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
by (hipster_induct_schemes insort.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes insort.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes insort.simps)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops

lemma unknown [thy_expl]: "insort Z (insort x y) = insort x (insort Z y)"
oops

(*hipster len sort*)
lemma lemma_ac [thy_expl]: "insort Z (sort x2) = sort (insort Z x2)"
by (hipster_induct_schemes len.simps sort.simps)

lemma unknown [thy_expl]: "sort (insort x y) = insort x (sort y)"
oops

lemma unknown [thy_expl]: "sort (sort x) = sort x"
oops

(*hipster_cond le*)
lemma lemma_ad [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_af [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_ag [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

(*lemma le_a : "(le (S Z) (S x) = True)"
by (tactic {* Tactic_Data.routine_tac @{context}*})

lemma le_aa []: "(le x y \<Longrightarrow> le x (S y))"
by (tactic {* Tactic_Data.routine_tac @{context}*})

lemma le_ac: "(le x y \<Longrightarrow> le (S x) (S y) = True)"
by (tactic {* Tactic_Data.routine_tac @{context}*})*)

(* false:
lemma le_ai: "(le x y \<and> le x z \<Longrightarrow> le x (S Z) = True)"
by (hipster_induct_schemes le.simps Nat.exhaust)*)

(*hipster len insort le*)
lemma lemma_ah [thy_expl]: "S (len x5) = len (insort y5 x5)"
by (hipster_induct_schemes len.simps insort.simps le.simps)

lemma lemma_ai [thy_expl]: "insort Z (insort x2 y2) = insort x2 (insort Z y2)"
by (hipster_induct_schemes len.simps insort.simps le.simps)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops


  theorem x0 :                      
    "(len (sort xs)) = (len xs)"
    by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)
end
