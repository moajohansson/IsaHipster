theory prop_32
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
  fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
  | "rotate (S z) (nil) = nil"
  | "rotate (S z) (cons x2 x3) =
       rotate z (append x3 (cons x2 (nil)))"
  theorem x0 :
    "!! (x :: 'a list) . (rotate (length x) x) = x"
    oops
end
