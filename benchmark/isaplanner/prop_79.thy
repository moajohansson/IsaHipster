theory prop_79
imports Main
imports "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  hipster minus
  theorem x0 :
    "!! (m :: Nat) (n :: Nat) (k :: Nat) .
       (minus (minus (S m) n) (S k)) = (minus (minus m n) k)"
    oops
end
