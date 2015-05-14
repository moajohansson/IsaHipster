theory prop_20
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
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (nil) = cons x (nil)"
  | "insort x (cons z xs) =
       (if le x z then cons x (cons z xs) else cons z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (nil) = nil"
  | "sort (cons y xs) = insort y (sort xs)"
  theorem x0 :
    "!! (xs :: Nat list) . (len (sort xs)) = (len xs)"
    oops
end
