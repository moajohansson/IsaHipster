theory nat_acc_alt_mul_comm
imports Main
        "../../IsaHipster"
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
    "(accaltmul x y) = (accaltmul y x)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
