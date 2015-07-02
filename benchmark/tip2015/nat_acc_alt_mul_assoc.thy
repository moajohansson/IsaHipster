theory nat_acc_alt_mul_assoc
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

fun accaltmul :: "Nat => Nat => Nat" where
"accaltmul (Z) y = Z"
| "accaltmul (S z) (Z) = Z"
| "accaltmul (S z) (S x2) =
     S (accplus z (accplus x2 (accaltmul z x2)))"

(*hipster accplus accaltmul *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat) (z :: Nat) .
     (accaltmul x (accaltmul y z)) = (accaltmul (accaltmul x y) z)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
