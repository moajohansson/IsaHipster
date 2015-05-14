theory prop_07
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil) y = y"
  | "qrev (cons z xs) y = qrev xs (cons z y)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (length (qrev x y)) = (plus (length x) (length y))"
    oops
end
