theory prop_22
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun even :: "Nat => bool" where
  "even (Z) = True"
  | "even (S (Z)) = False"
  | "even (S (S z)) = even z"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (even (length (append x y))) = (even (length (append y x)))"
    oops
end
