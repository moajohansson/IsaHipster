theory nat_acc_alt_mul_same
imports Main
        "../../IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun mult :: "Nat => Nat => Nat" where
"mult (Z) y = Z"
| "mult (S n) y = plus y (mult n y)"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

fun accaltmul :: "Nat => Nat => Nat" where
"accaltmul (Z) y = Z"
| "accaltmul (S z) (Z) = Z"
| "accaltmul (S z) (S x2) =
     S (accplus z (accplus x2 (accaltmul z x2)))"

(*hipster plus mult accplus accaltmul *)

theorem x0 :
  "!! (x :: Nat) . !! (y :: Nat) . (accaltmul x y) = (mult x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
