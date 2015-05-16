theory nat_pow_times
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S n) y = plus y (mult n y)"
  fun pow :: "Nat => Nat => Nat" where
  "pow x (Z) = S Z"
  | "pow x (S m) = mult x (pow x m)"
  hipster plus mult pow
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) (z :: Nat) .
       (pow x (plus y z)) = (mult (pow x y) (pow x z))"
    oops
end
