theory prop_24
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun even :: "Nat => bool" where
  "even (Z) = True"
  | "even (S (Z)) = False"
  | "even (S (S z)) = even z"
  hipster plus even
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) . (even (plus x y)) = (even (plus y x))"
    oops
end
