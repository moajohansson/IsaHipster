theory weird_nat_op_comm_comm
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun op :: "Nat => Nat => Nat => Nat => Nat" where
  "op (Z) y (Z) x2 = x2"
  | "op (Z) y (S x3) x2 = op Z y x3 (S x2)"
  | "op (S x4) y (Z) x2 = op x4 y y x2"
  | "op (S x4) y (S c) x2 = op (S x4) y c (S x2)"
  hipster op
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) (c :: Nat) (d :: Nat) .
       (op a b c d) = (op b a d c)"
    oops
end
