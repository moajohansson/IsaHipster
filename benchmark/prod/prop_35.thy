theory prop_35
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun one :: "Nat" where
  "one = S Z"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S z) y = plus y (mult z y)"
  fun qexp :: "Nat => Nat => Nat => Nat" where
  "qexp x (Z) z = z"
  | "qexp x (S n) z = qexp x n (mult x z)"
  fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
  | "exp x (S n) = mult x (exp x n)"
  hipster plus one mult qexp exp
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (exp x y) = (qexp x y one)"
    oops
end
