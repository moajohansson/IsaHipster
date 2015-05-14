theory nat_alt_mul_comm
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun altmul :: "Nat => Nat => Nat" where
  "altmul (Z) y = Z"
  | "altmul (S z) (Z) = Z"
  | "altmul (S z) (S x2) = S (plus (plus (altmul z x2) z) x2)"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (altmul x y) = (altmul y x)"
    oops
end
