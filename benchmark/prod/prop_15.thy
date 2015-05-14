theory prop_15
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  theorem x0 :
    "!! (x :: Nat) . (plus x (S x)) = (S (plus x x))"
    oops
end
