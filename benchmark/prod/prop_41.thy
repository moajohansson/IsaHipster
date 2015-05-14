theory prop_41
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
  fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (nil) y = nil"
  | "intersect (cons z xs) y =
       (if elem z y then cons z (intersect xs y) else intersect xs y)"
  fun subset :: "Nat list => Nat list => bool" where
  "subset (nil) y = True"
  | "subset (cons z xs) y =
       (if elem z y then subset xs y else False)"
  theorem x0 :
    "!! (x :: Nat list) (y :: Nat list) .
       (subset x y) ==> ((intersect x y) = x)"
    oops
end
