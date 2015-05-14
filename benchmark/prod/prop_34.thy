theory prop_34
imports Main
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun mult2 :: "Nat => Nat => Nat" where
  "mult2 (Z) y = Z"
  | "mult2 (S z) y = plus y (mult2 z y)"
  fun mult :: "Nat => Nat => Nat => Nat" where
  "mult (Z) y z = z"
  | "mult (S x2) y z = mult x2 y (plus y z)"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (mult2 x y) = (mult x y Z)"
    oops
end
