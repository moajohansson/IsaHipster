theory weird_nat_add3_assoc3
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun add3 :: "Nat => Nat => Nat => Nat" where
  "add3 (Z) (Z) z = z"
  | "add3 (Z) (S y2) z = S (add3 Z y2 z)"
  | "add3 (S x2) y z = S (add3 x2 y z)"
  hipster add3
  theorem x0 :
    "!! (x1 :: Nat) (x2 :: Nat) (x3 :: Nat) (x4 :: Nat) (x5 :: Nat) .
       (add3 x1 (add3 x2 x3 x4) x5) = (add3 x1 x2 (add3 x3 x4 x5))"
    oops
end
