theory nat_acc_plus_comm
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun accplus :: "Nat => Nat => Nat" where
"accplus (Z) y = y"
| "accplus (S z) y = accplus z (S y)"

(*hipster accplus *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat) . (accplus x y) = (accplus y x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
