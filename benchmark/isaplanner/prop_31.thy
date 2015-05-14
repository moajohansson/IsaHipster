theory prop_31
imports Main
imports "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
  | "min2 (S z) (Z) = Z"
  | "min2 (S z) (S y1) = S (min2 z y1)"
  hipster min2
  theorem x0 :
    "!! (a :: Nat) (b :: Nat) (c :: Nat) .
       (min2 (min2 a b) c) = (min2 a (min2 b c))"
    oops
end
