theory fermat_last
imports Main
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
  theorem x0 :
    "!! (n :: Nat) (x :: Nat) (y :: Nat) (z :: Nat) .
       ((plus (pow (S x) (S (S (S n)))) (pow (S y) (S (S (S n))))) =
          (pow (S z) (S (S (S n))))) ==>
         False"
    oops
end
