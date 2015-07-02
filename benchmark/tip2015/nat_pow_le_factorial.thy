theory nat_pow_le_factorial
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun mult :: "Nat => Nat => Nat" where
"mult (Z) y = Z"
| "mult (S n) y = plus y (mult n y)"

fun pow :: "Nat => Nat => Nat" where
"pow x (Z) = S Z"
| "pow x (S m) = mult x (pow x m)"

fun lt :: "Nat => Nat => bool" where
"lt (Z) y = True"
| "lt (S z) (Z) = False"
| "lt (S z) (S x2) = lt z x2"

fun factorial :: "Nat => Nat" where
"factorial (Z) = S Z"
| "factorial (S n) = mult (S n) (factorial n)"

(*hipster plus mult pow lt factorial *)

theorem x0 :
  "!! (n :: Nat) .
     lt (pow (S (S Z)) (S (S (S (S n))))) (factorial (S (S (S (S n)))))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
