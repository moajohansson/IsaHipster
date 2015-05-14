theory prop_30
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (nil) = cons x (nil)"
  | "ins x (cons z xs) =
       (if lt x z then cons x (cons z xs) else cons z (ins x xs))"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z xs) = (if equal2 x z then True else elem x xs)"
  hipster lt ins equal2 elem
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . elem x (ins x xs)"
    oops
end
