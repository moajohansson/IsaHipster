theory A
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  theorem x0 :
    "!! (m :: Nat) (n :: Nat) (k :: Nat) .
       (minus (minus (S m) n) (S k)) = (minus (minus m n) k)"
    oops
end
