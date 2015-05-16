theory prop_10
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  hipster minus
  theorem x0 :
    "!! (m :: Nat) . (minus m m) = Z"
    oops
end
