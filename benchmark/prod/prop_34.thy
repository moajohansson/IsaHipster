theory prop_34
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun mult2 :: "Nat => Nat => Nat" where
  "mult2 (Z) y = Z"
  | "mult2 (S z) y = plus y (mult2 z y)"
  fun mult :: "Nat => Nat => Nat => Nat" where
  "mult (Z) y z = z"
  | "mult (S x2) y z = mult x2 y (plus y z)"
  (*hipster plus mult2 mult *)
  theorem x0 :
    "(mult2 x y) = (mult x y Z)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
