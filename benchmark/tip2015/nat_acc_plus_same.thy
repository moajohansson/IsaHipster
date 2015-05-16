theory nat_acc_plus_same
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun accplus :: "Nat => Nat => Nat" where
  "accplus (Z) y = y"
  | "accplus (S z) y = accplus z (S y)"
  (*hipster plus accplus *)
  theorem x0 :
    "(plus x y) = (accplus x y)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
