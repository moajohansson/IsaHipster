theory A
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun max2 :: "Nat => Nat => Nat" where
  "max2 (Z) y = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) (c :: Nat) .
       (max2 (max2 a b) c) = (max2 a (max2 b c))"
    oops
end
