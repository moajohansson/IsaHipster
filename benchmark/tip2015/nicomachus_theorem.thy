theory nicomachus_theorem
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun sum :: "Nat => Nat" where
"sum (Z) = Z"
| "sum (S n) = plus (sum n) (S n)"

fun mult :: "Nat => Nat => Nat" where
"mult (Z) y = Z"
| "mult (S n) y = plus y (mult n y)"

fun cubes :: "Nat => Nat" where
"cubes (Z) = Z"
| "cubes (S n) = plus (cubes n) (mult (mult (S n) (S n)) (S n))"

(*hipster plus sum mult cubes *)
lemma lemma_a [thy_expl]: "plus x2 Z = x2"
by (hipster_induct_schemes plus.simps)

lemma lemma_aa [thy_expl]: "plus (plus x2 y2) z2 = plus x2 (plus y2 z2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ab [thy_expl]: "plus x2 (S y2) = S (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ac [thy_expl]: "plus x1 (plus y1 x1) = plus y1 (plus x1 x1)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ad [thy_expl]: "plus x2 (plus y2 y2) = plus y2 (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ae [thy_expl]: "plus x2 (S y2) = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_af [thy_expl]: "plus (S x2) y2 = S (plus y2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ag [thy_expl]: "plus (plus x2 y2) (plus x2 z2) = plus (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps Nat.exhaust)

lemma lemma_ah [thy_expl]: "plus (plus x2 y2) (plus z2 x2) = plus (plus z2 x2) (plus x2 y2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_ai [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus z2 x2)"
by (hipster_induct_schemes plus.simps)

lemma lemma_aj [thy_expl]: "plus x2 y2 = plus y2 x2"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ak [thy_expl]: "mult x2 Z = Z"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_al [thy_expl]: "mult x1 (S y1) = plus x1 (mult x1 y1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_am [thy_expl]: "mult x2 (plus y2 y2) = mult y2 (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_an [thy_expl]: "mult x2 (S y2) = plus x2 (mult y2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ao [thy_expl]: "mult (plus x2 y2) x2 = mult x2 (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps Nat.exhaust)

lemma lemma_ap [thy_expl]: "mult (mult x1 y1) x1 = mult x1 (mult x1 y1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_aq [thy_expl]: "mult (plus x2 x2) y2 = mult x2 (plus y2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ar [thy_expl]: "mult (mult x2 x2) y2 = mult y2 (mult x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_as [thy_expl]: "plus (mult x1 y1) (mult y1 z1) = mult y1 (plus x1 z1)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_at [thy_expl]: "plus (mult x2 y2) (mult z2 x2) = mult x2 (plus z2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_au [thy_expl]: "mult (plus x2 y2) (plus x2 z2) = mult (plus x2 z2) (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_av [thy_expl]: "mult (plus x2 y2) (plus z2 y2) = mult (plus z2 y2) (plus x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_aw [thy_expl]: "mult (mult x2 y2) (plus x2 z2) = mult (plus x2 z2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ax [thy_expl]: "mult (mult x2 y2) (plus y2 z2) = mult (plus y2 z2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ay [thy_expl]: "mult (mult x2 y2) (mult z2 x2) = mult (mult z2 x2) (mult x2 y2)"
by (hipster_induct_schemes mult.simps plus.simps Nat.exhaust)

lemma lemma_az [thy_expl]: "mult (plus x2 x2) (plus y2 z2) = mult (plus y2 z2) (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_ba [thy_expl]: "mult (plus x2 x2) (mult y2 z2) = mult (mult y2 z2) (plus x2 x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bb [thy_expl]: "mult (S x2) (S y2) = mult (S y2) (S x2)"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bc [thy_expl]: "mult x2 y2 = mult y2 x2"
by (hipster_induct_schemes mult.simps plus.simps)

lemma lemma_bd [thy_expl]: "mult x2 (mult y2 z2) = mult y2 (mult x2 z2)"
by (hipster_induct_schemes mult.simps plus.simps Nat.exhaust)

lemma lemma_be [thy_expl]: "plus (mult x1 y1) (mult x1 z1) = mult x1 (plus y1 z1)"
by (hipster_induct_schemes mult.simps plus.simps)


(*hipster mult plus sum*)
lemma lemma_bf [thy_expl]: "plus (sum x1) (sum x1) = plus x1 (mult x1 x1)"
by (hipster_induct_schemes mult.simps plus.simps sum.simps Nat.exhaust)

(*hipster cubes mult plus sum*)
lemma lemma_bg [thy_expl]: "mult (plus x1 x1) (sum y1) = mult (mult x1 y1) (S y1)"
by (hipster_induct_schemes cubes.simps mult.simps plus.simps sum.simps)

lemma lemma_bh [thy_expl]: "mult (plus x1 x1) (sum y1) = mult (mult y1 x1) (S y1)"
by (hipster_induct_schemes cubes.simps mult.simps plus.simps sum.simps)

lemma lemma_bi [thy_expl]: "mult (S x3) (mult x3 x3) = mult (plus x3 x3) (sum x3)"
by (hipster_induct_schemes cubes.simps plus.simps mult.simps sum.simps)


(*hipster mult plus sum cubes*)

lemma lemma_ai2 [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus x2 z2)"
by (hipster_induct_schemes plus.simps)

(*mult (sum x) (sum x) = cubes x \<Longrightarrow>
         S (plus (plus x (sum x)) (mult (plus x (sum x)) (S (plus x (sum x))))) =
         plus (cubes x) (S (plus (plus x (mult x (S x))) (mult x (S (plus x (mult x (S x))))))*)

lemma unknown [thy_expl]: "mult (sum x) (sum x) = cubes x"
apply(induction x)
apply simp_all
apply(simp_all add: lemma_bf lemma_be lemma_bc lemma_aj lemma_ai2)
(*sledgehammer*)
apply (metis mult.simps sum.simps cubes.simps plus.simps Nat.exhaust lemma_aa lemma_ab lemma_ai2 lemma_aj lemma_al lemma_as lemma_bc lemma_be lemma_bf)
done
(*lemma lemma_ai [thy_expl]: "plus x2 (plus y2 z2) = plus y2 (plus z2 x2)"
*)
theorem x0 :
  "!! (n :: Nat) . (cubes n) = (mult (sum n) (sum n))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
