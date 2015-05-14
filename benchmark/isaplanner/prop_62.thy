theory prop_62
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun null :: "'a list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun last :: "Nat list => Nat" where
  "last (nil) = Z"
  | "last (cons y (nil)) = y"
  | "last (cons y (cons x2 x3)) = last (cons x2 x3)"
  theorem x0 :
    "!! (xs :: Nat list) (x :: Nat) .
       (~ (null xs)) ==> ((last (cons x xs)) = (last xs))"
    oops
end
