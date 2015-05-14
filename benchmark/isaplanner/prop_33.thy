theory A
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
  | "min2 (S z) (Z) = Z"
  | "min2 (S z) (S y1) = S (min2 z y1)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) . (equal2 (min2 a b) a) = (le a b)"
    oops
end
