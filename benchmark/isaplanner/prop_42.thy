theory prop_42
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  theorem x0 :
    "!! (n :: Nat) (x :: 'a) (xs :: 'a list) .
       (take (S n) (cons x xs)) = (cons x (take n xs))"
    oops
end
