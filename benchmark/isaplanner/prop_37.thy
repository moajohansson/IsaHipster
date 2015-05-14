theory A
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
  fun delete :: "Nat => Nat list => Nat list" where
  "delete x (nil) = nil"
  | "delete x (cons z xs) =
       (if equal2 x z then delete x xs else cons z (delete x xs))"
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . ~ (elem x (delete x xs))"
    oops
end
