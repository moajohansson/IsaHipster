theory nat_alt_mul_same
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

fun altmul :: "Nat => Nat => Nat" where
"altmul (Z) y = Z"
| "altmul (S z) (Z) = Z"
| "altmul (S z) (S x2) = S (plus (plus (altmul z x2) z) x2)"

(*hipster plus mult altmul *)

theorem x0 :
  "!! (x :: Nat) . !! (y :: Nat) . (altmul x y) = (mult x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
