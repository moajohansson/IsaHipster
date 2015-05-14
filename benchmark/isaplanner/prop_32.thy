theory A
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
  | "min2 (S z) (Z) = Z"
  | "min2 (S z) (S y1) = S (min2 z y1)"
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) . (min2 a b) = (min2 b a)"
    oops
end
