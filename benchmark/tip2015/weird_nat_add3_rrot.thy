theory weird_nat_add3_rrot
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun add3 :: "Nat => Nat => Nat => Nat" where
  "add3 (Z) (Z) z = z"
  | "add3 (Z) (S y2) z = S (add3 Z y2 z)"
  | "add3 (S x2) y z = S (add3 x2 y z)"
  (*hipster add3 *)
  theorem x0 :
    "(add3 x y z) = (add3 z x y)"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
