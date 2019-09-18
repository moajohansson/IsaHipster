theory addMul

imports Main
        "../Naturals"

begin

(*hipster add mul*)

lemma l01 [thy_expl] : "mul x Z = Z"
by hipster_induct_simp_metis

lemma l02 [thy_expl] : "add x Z = x"
by hipster_induct_simp_metis

lemma l03 [thy_expl] : "add (add x y) z = add x (add y z)"
by hipster_induct_simp_metis
(* by (tactic {* Simp_Tacs.routine_tac @{context} *}) *)

lemma l04 [thy_expl] : "add x (S y) = S (add x y)"
by hipster_induct_simp_metis

lemma l05 [thy_expl] : "add x (add y x) = add y (add x x)"
by hipster_induct_simp_metis

lemma l06 [thy_expl] : "add x (add y y) = add y (add y x)"
by hipster_induct_simp_metis

lemma l07 [thy_expl] : "add x (S y) = S (add y x)"
by hipster_induct_simp_metis


lemma l08' [thy_expl] : "add (mul x y) x = mul x (S y)"
by (hipster_induct_simp_metis l03 l04)

(*lemma l08 [thy_expl] : "add (mul x y) x = mul x (S y)"
(*apply (hipster_induct_schemes add.simps mul.simps l07 l03 l04)*)
(*apply (tactic {* Hipster_Explore.explore_goal @{context} ["Naturals.add", "Naturals.mul"] *})*)
sorry (*by (hipster_induct_schemes add.simps mul.simps l07 l03 l04)*)*)

lemma t01 : "add (add x y) x = add x (add x y)"
by hipster_induct_simp_metis

lemma t02 : "add (add x y) y = add x (add y y)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma l09 [thy_expl] : "mul (add x x) y = mul x (add y y)"
by hipster_induct_simp_metis

lemma l10 [thy_expl] : "mul (add x x) y = mul y (add x x)"
by hipster_induct_simp_metis

lemma l11 [thy_expl] : "add (mul x x) y = add y (mul x x)"
by hipster_induct_simp_metis

lemma t03 : "add (add x x) y = add x (add x y)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t04 : "add (add x x) y = add y (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma l12 [thy_expl] : "add (S x) y = S (add y x)"
by hipster_induct_simp_metis

lemma t05  : "add x (mul x x) = mul x (S x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)  (* follows from the incomplete one *)

lemma t06 : "add x (S x) = S (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t07 : "mul (mul x x) x = mul x (mul x x)"
by hipster_induct_simp_metis

lemma t07b : "mul (add x x) x = mul x (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t08 : "mul (S x) x = mul x (S x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t09 : "add (mul x x) x = mul x (S x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t10 : "add (add x x) x = add x (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma l13 [thy_expl] : "add (mul x y) (mul x z) = mul x (add y z)"
by hipster_induct_simp_metis

lemma l14 [thy_expl] : "add (mul x y) (mul y z) = mul y (add x z)"
by hipster_induct_simp_metis

lemma l15 [thy_expl] : "add (mul x y) (mul x z) = mul x (add z y)"
by hipster_induct_simp_metis

lemma t11 : "add (mul x y) (mul z y) = mul y (add x z)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t12 : "add (mul x y) (mul z x) = mul x (add z y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t13 : "add (mul x y) (mul z y) = mul y (add z x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t14 : "add (add x y) (mul x z) = add (mul x z) (add x y)"
by hipster_induct_simp_metis

lemma t15 : "add (add x y) (mul y z) = add (mul y z) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t16 : "add (add x y) (mul z y) = add (mul z y) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t17 : "add (add x y) (add x z) = add (add x z) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t18 : "add (add x y) (add z y) = add (add x z) (add y y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t19 : "add (add x y) (add z z) = add (add x z) (add z y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t20 : "add (add x y) (S z) = add (add x z) (S y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t21 : "add (add x y) (mul z x) = add (mul z x) (add x y)"
by hipster_induct_simp_metis

lemma t22 : "add (add x y) (add z x) = add (add z x) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t23 : "add (add x y) (add z y) = add (add z x) (add y y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t24 : "add (add x y) (add z z) = add (add z x) (add z y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t25 : "add (add x y) (S z) = add (add z x) (S y)"
by hipster_induct_simp_metis

lemma t26 : "mul (mul x x) (add y z) = mul (add y z) (mul x x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t27 : "mul (mul x x) (mul y z) = mul (mul y z) (mul x x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma l16 : "mul (add x x) (add y z) = mul (add y z) (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t28 : "mul (add x x) (mul y z) = mul (mul y z) (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t29 : "mul (S x) (mul y z) = mul (mul y z) (S x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t30 : "mul (S x) (add y z) = mul (add y z) (S x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t31 : "add (mul x x) (mul y z) = add (mul y z) (mul x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t32 : "add (mul x x) (add y z) = add (add y z) (mul x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t33 : "add (add x x) (mul y z) = add (mul y z) (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t34 : "add (add x x) (add y z) = add (add x y) (add x z)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t35 : "add (add x x) (add y z) = add (add y x) (add x z)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t36 : "add (add x x) (add y z) = add (add y z) (add x x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t37 : "add (S x) (mul y z) = add (mul y z) (S x)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t38 : "add (S x) (add y z) = add (add x y) (S z)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t39 : "add (S x) (add y z) = add (add y x) (S z)"
by hipster_induct_simp_metis

lemma l17 [thy_expl] : "add (S x) (add y z) = add (add y z) (S x)"
by hipster_induct_simp_metis

lemma t40 : "mul (mul x y) Z = Z"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t41 : "mul (add x y) Z = Z"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma l18 [thy_expl]  : "mul (add x y) (mul x y) = mul (mul x y) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t42 : "add (mul x y) Z = mul x y"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t43 : "add (mul x y) (mul x y) = mul x (add y y)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t44 : "add (mul x y) (mul x x) = mul x (add x y)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t45 : "add (mul x y) (mul y y) = mul y (add x y)"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t46 : "add (add x y) Z = add x y"
by (tactic \<open>Simp_Tacs.routine_tac @{context}\<close>)

lemma t47 : "add (add x y) (mul x y) = add (mul x y) (add x y)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma t48 : "mul (mul x x) (mul x y) = mul (mul x y) (mul x x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)

lemma l19 [thy_expl] : "mul (mul x x) (add x y) = mul (add x y) (mul x x)"
by (tactic \<open>Ind_Schemes_Tacs.routine_tac @{context}\<close>)


end
