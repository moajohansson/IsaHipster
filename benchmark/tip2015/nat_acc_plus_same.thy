theory nat_acc_plus_same
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun accplus :: "Nat => Nat => Nat" where
  "accplus (Z) y = y"
  | "accplus (S z) y = accplus z (S y)"
  theorem x0 :
    "!! (x :: Nat) . !! (y :: Nat) . (plus x y) = (accplus x y)"
    oops
end
