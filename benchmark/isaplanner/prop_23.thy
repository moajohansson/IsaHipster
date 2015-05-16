theory prop_23
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun max2 :: "Nat => Nat => Nat" where
  "max2 (Z) y = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  hipster max2
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) . (max2 a b) = (max2 b a)"
    oops
end
