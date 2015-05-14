theory prop_16
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (nil) = Z"
  | "last (cons y (nil)) = y"
  | "last (cons y (cons x2 x3)) = last (cons x2 x3)"
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) .
       (xs = (nil)) ==> ((last (cons x xs)) = x)"
    oops
end
