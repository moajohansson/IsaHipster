theory prop_10
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  (*hipster minus *)
  theorem x0 :
    "(minus m m) = Z"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
