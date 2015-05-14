theory prop_64
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (nil) = Z"
  | "last (cons y (nil)) = y"
  | "last (cons y (cons x2 x3)) = last (cons x2 x3)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) .
       (last (append xs (cons x (nil)))) = x"
    oops
end
