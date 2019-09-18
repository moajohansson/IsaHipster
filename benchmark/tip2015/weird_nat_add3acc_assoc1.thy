theory weird_nat_add3acc_assoc1
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun add3acc :: "Nat => Nat => Nat => Nat" where
"add3acc (Z) (Z) z = z"
| "add3acc (Z) (S y2) z = add3acc Z y2 (S z)"
| "add3acc (S x2) y z = add3acc x2 (S y) z"

(*hipster add3acc *)

theorem x0 :
  "!! (x1 :: Nat) (x2 :: Nat) (x3 :: Nat) (x4 :: Nat) (x5 :: Nat) .
     (add3acc (add3acc x1 x2 x3) x4 x5) =
       (add3acc x1 x2 (add3acc x3 x4 x5))"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
