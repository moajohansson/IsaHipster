theory A
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
  fun filter :: "'a => bool => 'a list => 'a list" where
  "filter x (nil) = nil"
  | "filter x (cons z xs) =
       (if x z then cons z (filter x xs) else filter x xs)"
  theorem x0 :
    "!! (q :: 'a => bool) (xs :: 'a list) .
       le (len (filter q xs)) (len xs)"
    oops
end
