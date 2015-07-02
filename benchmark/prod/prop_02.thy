theory prop_02
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "Nat list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun append :: "Nat list => Nat list => Nat list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster length append *)

lemma ruledd: "P Nil2 Nil2 \<Longrightarrow> (\<And>x xs. P (xs) Nil2 \<Longrightarrow> P (Cons2 x xs) Nil2)
                  \<Longrightarrow> (\<And> y ys. P Nil2 ys \<Longrightarrow> P Nil2 (Cons2 y ys))
                  \<Longrightarrow> (\<And> x xs y ys. P xs ys \<Longrightarrow> P (Cons2 x xs) (Cons2 y ys)) \<Longrightarrow> (\<And> xs ys. P xs ys)"
oops

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes length.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes length.simps append.simps)

lemma unknown []: "length (append x y) = length (append y x)"
oops

(*lemma ax: "length (append (Cons2 ya xs) y) = S (length (append xs y))"
by (metis length.simps(2) append.simps(2))

lemma ax2[thy_expl]: "length (append y (Cons2 ya xs)) = S (length (append y xs))"
by(hipster_induct_schemes)
*)
fun toL :: "Nat \<Rightarrow> Nat list" where
"toL Z = Nil2"
| "toL (S x) = Cons2 x (toL x)"

hipster length append toL
lemma lemma_ab [thy_expl]: "prop_02.length (toL x2) = x2"
by (hipster_induct_schemes prop_02.length.simps prop_02.append.simps prop_02.toL.simps)

lemma unknown [thy_expl]: "prop_02.length (prop_02.append x y) = prop_02.length (prop_02.append y x)"
oops

lemma s:  "(length (append x y)) = (length (append y x))"
apply(induction x arbitrary:y)
apply simp_all
apply(case_tac y)
apply simp_all
apply(metis thy_expl length.simps append.simps)
oops

  theorem x0 :
    "(length (append x y)) = (length (append y x))"
    apply(induction x arbitrary: y)
    apply simp_all
    apply(induction y)
    apply simp_all
    by(hipster_induct_schemes length.simps append.simps)
    (*apply(hipster_induct_schemes length.simps append.simps thy_expl list.exhaust)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
