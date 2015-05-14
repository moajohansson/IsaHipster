theory prop_02
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (x :: 'a list) (y :: 'a list) .
       (length (append x y)) = (length (append y x))"
    oops
end
