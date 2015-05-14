theory weird_nat_mul2_comm
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun add3acc :: "Nat => Nat => Nat => Nat" where
  "add3acc (Z) (Z) z = z"
  | "add3acc (Z) (S y2) z = add3acc Z y2 (S z)"
  | "add3acc (S x2) y z = add3acc x2 (S y) z"
  fun mul2 :: "Nat => Nat => Nat" where
  "mul2 (Z) y = Z"
  | "mul2 (S z) (Z) = Z"
  | "mul2 (S z) (S x2) = S (add3acc z x2 (mul2 z x2))"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (mul2 x y) = (mul2 y x)"
    oops
end
