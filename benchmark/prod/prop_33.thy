theory prop_33
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
  fun qfac :: "Nat => Nat => Nat" where
  "qfac (Z) y = y"
  | "qfac (S z) y = qfac z (mult (S z) y)"
  fun fac :: "Nat => Nat" where
  "fac (Z) = S Z"
  | "fac (S y) = mult (S y) (fac y)"
  hipster plus one mult qfac fac
  theorem x0 :
    "!! (x :: Nat) . (fac x) = (qfac x one)"
    oops
end
