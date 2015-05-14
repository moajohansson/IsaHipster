theory nat_acc_plus_comm
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun accplus :: "Nat => Nat => Nat" where
  "accplus (Z) y = y"
  | "accplus (S z) y = accplus z (S y)"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (accplus x y) = (accplus y x)"
    oops
end
