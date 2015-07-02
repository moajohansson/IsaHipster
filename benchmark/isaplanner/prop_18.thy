theory prop_18
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  (*hipster plus lt *)
  theorem x0 :
    "lt i (S (plus i m))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
