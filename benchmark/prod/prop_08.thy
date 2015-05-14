theory prop_08
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) (z :: 'a list) .
       (drop x (drop y z)) = (drop y (drop x z))"
    oops
end
