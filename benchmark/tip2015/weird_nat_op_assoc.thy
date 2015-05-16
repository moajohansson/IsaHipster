theory weird_nat_op_assoc
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun op :: "Nat => Nat => Nat => Nat => Nat" where
  "op (Z) y (Z) x2 = x2"
  | "op (Z) y (S x3) x2 = op Z y x3 (S x2)"
  | "op (S x4) y (Z) x2 = op x4 y y x2"
  | "op (S x4) y (S c) x2 = op (S x4) y c (S x2)"
  (*hipster op *)
  theorem x0 :
    "(op (op a b Z Z) c d e) = (op a (op b c Z Z) d e)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
