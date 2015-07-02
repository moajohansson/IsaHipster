theory nat_acc_plus_assoc
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

(*hipster accplus *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat) (z :: Nat) .
     (accplus x (accplus y z)) = (accplus (accplus x y) z)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
