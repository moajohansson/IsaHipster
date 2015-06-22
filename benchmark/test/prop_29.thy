theory prop_29
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun ins1 :: "Nat => Nat list => Nat list" where
  "ins1 x (nil) = cons x (nil)"
  | "ins1 x (cons z xs) =
       (if equal2 x z then cons z xs else cons z (ins1 x xs))"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z xs) = (if equal2 x z then True else elem x xs)"
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . elem x (ins1 x xs)"
    oops
end
