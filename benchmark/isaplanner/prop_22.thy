theory prop_22
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun max2 :: "Nat => Nat => Nat" where
    (*"max2 Z Z = Z"*)
    "max2 (Z) ( y) = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  (*hipster max2 *)
thm max2.induct
(*
lemma lemma_a [thy_expl]: "max2 x x = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_aa [thy_expl]: "max2 x Z = x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ab [thy_expl]: "max2 x (max2 x y) = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ac [thy_expl]: "max2 x (max2 y x) = max2 y x"
by (hipster_induct_schemes max2.simps)

lemma lemma_ad [thy_expl]: "max2 (max2 x y) x = max2 x y"
by (hipster_induct_schemes max2.simps)

lemma lemma_ae []: "max2 (S x) y = max2 y (S x)"
by (hipster_induct_schemes max2.simps)

lemma lemma_af []: "max2 x y = max2 y x"
by (hipster_induct_schemes max2.simps)
*)
lemma lemma_a [thy_expl]: "max2 x2 y2 = max2 y2 x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_aa [thy_expl]: "max2 x2 x2 = x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ab [thy_expl]: "max2 x2 Z = x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ac [thy_expl]: "max2 x1 (max2 x1 y1) = max2 x1 y1"
by (hipster_induct_schemes max2.simps)

lemma lemma_ad [thy_expl]: "max2 x2 (S x2) = S x2"
by (hipster_induct_schemes max2.simps)

lemma lemma_ae [thy_expl]: "max2 (max2 x1 y1) (S x1) = max2 y1 (S x1)"
by (hipster_induct_schemes max2.simps)

(*
lemma dd :"max2 (S x) x = S x"
by hipster_induct_simp_metis

lemma triv_a []: "max2 (max2 x y) y = max2 x y"
by (tactic {* Tactic_Data.routine_tac @{context}*})
*)
(*
lemma ax:"max2 (max2 x y) (max2 y z) = max2 x (max2 y z)"
apply(induction y z rule: max2.induct)
apply(simp_all add: lemma_aa lemma_ad triv_a)

apply (simp_all add:lemma_aa lemma_a lemma_ab lemma_ac lemma_ad dd triv_a)
lemma aa: "max2 (max2 a b) c = max2 a (max2 b c) \<Longrightarrow> max2 (max2 a b) (S c) = max2 a (max2 b (S c))"
apply hipster_induct_schemes*)



  theorem x0 :
    "(max2 (max2 a b) c) = (max2 a (max2 b c))"
    by (hipster_induct_schemes max2.simps Nat.exhaust)

    apply(induction a b arbitrary: c rule: max2.induct)
    apply(simp_all)
    by (metis max2.simps Nat.exhaust)

    (*
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
