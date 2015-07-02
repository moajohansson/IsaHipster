theory weird_nat_add3_comm23
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun add3 :: "Nat => Nat => Nat => Nat" where
"add3 (Z) (Z) z = z"
| "add3 (Z) (S y2) z = S (add3 Z y2 z)"
| "add3 (S x2) y z = S (add3 x2 y z)"

(*hipster add3 *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat) (z :: Nat) . (add3 x y z) = (add3 x z y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
