theory prop_40
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z xs) = (if equal2 x z then True else elem x xs)"
  fun subset :: "Nat list => Nat list => bool" where
  "subset (nil) y = True"
  | "subset (cons z xs) y =
       (if elem z y then subset xs y else False)"
  fun union :: "Nat list => Nat list => Nat list" where
  "union (nil) y = y"
  | "union (cons z xs) y =
       (if elem z y then union xs y else cons z (union xs y))"
  theorem x0 :
    "!! (x :: Nat list) (y :: Nat list) .
       (subset x y) ==> ((union x y) = y)"
    oops
end
