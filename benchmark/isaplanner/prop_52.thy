theory prop_52
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  fun append :: "Nat list => Nat list => Nat list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "Nat list => Nat list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster equal2 count append rev *)

lemma lemma_a [thy_expl]: "equal2 x4 y4 = equal2 y4 x4"
by (hipster_induct_schemes prop_52.equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes prop_52.equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes prop_52.equal2.simps)

lemma lemma_pa [thy_expl]: "prop_52.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_52.rev.simps)

lemma lemma_paa [thy_expl]: "prop_52.append (prop_52.append x2 y2) z2 =
prop_52.append x2 (prop_52.append y2 z2)"
by (hipster_induct_schemes prop_52.rev.simps)

lemma lemma_pab [thy_expl]: "prop_52.append (prop_52.rev x5) (prop_52.rev y5) =
prop_52.rev (prop_52.append y5 x5)"
by (hipster_induct_schemes prop_52.rev.simps)

hipster count

(*hipster_cond equal2 count append*)
lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes prop_52.equal2.simps prop_52.count.simps prop_52.append.simps)

lemma missed: "equal2 x z \<Longrightarrow> count x (Cons2 z xs) = S (count z xs)"
by (hipster_induct_simp_metis count.simps equal2.simps)

lemma missed': "\<not> equal2 x z \<Longrightarrow> count x (Cons2 z xs) = count x xs"
by (hipster_induct_simp_metis count.simps equal2.simps)

lemma missed2: "S (count x (prop_52.append z ys)) = count x (prop_52.append z (Cons2 x ys))"
by hipster_induct_schemes

lemma aux2: "\<not> equal2 x za \<Longrightarrow> count x (prop_52.append z ys) = count x (prop_52.append z (Cons2 za ys))"
by hipster_induct_schemes

(*hipster count append*)
lemma could_not [thy_expl]: "count x (prop_52.append y z) = count x (prop_52.append z y)"
by (hipster_induct_schemes prop_52.equal2.simps prop_52.count.simps prop_52.append.simps missed2 aux2)


(*hipster append count*)
(*hipster count rev*)

  theorem x0 :
    "(count n xs) = (count n (rev xs))"
    by (hipster_induct_schemes rev.simps prop_52.count.simps prop_52.append.simps)
(*
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)

end
