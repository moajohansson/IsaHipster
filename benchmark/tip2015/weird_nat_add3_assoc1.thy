theory weird_nat_add3_assoc1
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
  "!! (x1 :: Nat) (x2 :: Nat) (x3 :: Nat) (x4 :: Nat) (x5 :: Nat) .
     (add3 (add3 x1 x2 x3) x4 x5) = (add3 x1 x2 (add3 x3 x4 x5))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
