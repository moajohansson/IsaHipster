theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun len :: "'a list => Nat" where
  "len (nil) = Z"
  | "len (cons y xs) = S (len xs)"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (nil) = cons x (nil)"
  | "ins x (cons z xs) =
       (if lt x z then cons x (cons z xs) else cons z (ins x xs))"
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . (len (ins x xs)) = (S (len xs))"
    oops
end
