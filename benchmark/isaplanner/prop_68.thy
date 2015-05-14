theory prop_68
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (nil) = Z"
  | "len (cons y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun delete :: "Nat => Nat list => Nat list" where
  "delete x (nil) = nil"
  | "delete x (cons z xs) =
       (if equal2 x z then delete x xs else cons z (delete x xs))"
  theorem x0 :
    "!! (n :: Nat) (xs :: Nat list) . le (len (delete n xs)) (len xs)"
    oops
end
