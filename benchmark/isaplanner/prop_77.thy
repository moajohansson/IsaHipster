theory prop_77
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
  | "sorted (Cons2 y (Nil2)) = True"
  | "sorted (Cons2 y (Cons2 y2 ys)) =
       (if le y y2 then sorted (Cons2 y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  (*hipster le sorted insort *)
(*hipster insort le*)
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes le.simps)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes le.simps)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops

lemma unknown [thy_expl]: "insort Z (insort x y) = insort x (insort Z y)"
oops

(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "le x2 y2 \<Longrightarrow> le x2 (S y2) = True"
by (hipster_induct_schemes le.simps)

lemma lemma_ad [thy_expl]: "le y2 x2 \<Longrightarrow> le (S x2) y2 = False"
by (hipster_induct_schemes le.simps)

lemma lemma_ae [thy_expl]: "le y x \<and> le x y \<Longrightarrow> x = y"
by (hipster_induct_schemes le.simps Nat.exhaust)

lemma lemma_af [thy_expl]: "le z y \<and> le x z \<Longrightarrow> le x y = True"
by (hipster_induct_schemes le.simps Nat.exhaust)

hipster insort le
lemma lemma_ag [thy_expl]: "insort Z (insort x2 y2) =
insort x2 (insort Z y2)"
by (hipster_induct_schemes insort.simps le.simps)

(*hipster_cond sorted insort*)
lemma lemma_ah [thy_expl]: "sorted (insort Z x4) = sorted x4"
by (hipster_induct_schemes sorted.simps insort.simps)

lemma unknown [thy_expl]: "insort x (insort y z) = insort y (insort x z)"
oops

lemma unknown [thy_expl]: "sorted (insort x y) = sorted y"
oops

fun nole:: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "nole x y = (\<not> le x y)"

(*hipster_cond nole*)
lemma lemma_ai [thy_expl]: "le (S x2) y2 = nole y2 x2"
by (hipster_induct_schemes nole.simps)

lemma lemma_aj [thy_expl]: "nole x2 y2 \<Longrightarrow> le x2 Z = False"
by (hipster_induct_schemes nole.simps)

lemma lemma_ak [thy_expl]: "sorted y \<Longrightarrow> sorted (insort x y) = True"
apply(induction y arbitrary: x rule: sorted.induct)
apply(simp_all)
apply(metis nole.simps thy_expl)
by(metis (full_types) thy_expl sorted.simps insort.simps nole.simps)

(*
lemma timpano []: "\<not> (le m n) \<Longrightarrow> le n m"
by (hipster_induct_schemes le.simps)
lemma tt []: "\<lbrakk> le m n; le n m \<rbrakk> \<Longrightarrow> m = n"
by (metis thy_expl)
by (hipster_induct_schemes le.simps Nat.exhaust)*)

  theorem x0 :
    "(sorted xs) ==> (sorted (insort x xs))"
    by (hipster_induct_schemes insort.simps sorted.simps)
    (*apply(induction xs rule:sorted.induct)
    apply (simp_all add: timpano)
    (*apply(metis sorted.simps insort.simps timpano thy_expl)*)
    (*apply(metis le.simps sorted.simps insort.simps thy_expl*)
    (*apply(metis insort.simps le.simps)*)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)

end


