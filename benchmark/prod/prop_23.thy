theory prop_23
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S z)) = S (half z)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (half (length (append x y))) = (half (length (append y x)))"
    oops
end
