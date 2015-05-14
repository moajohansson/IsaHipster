theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (nil) = Z"
  | "len (cons y xs) = S (len xs)"
  fun butlast :: "'a list => 'a list" where
  "butlast (nil) = nil"
  | "butlast (cons y (nil)) = nil"
  | "butlast (cons y (cons x2 x3)) = cons y (butlast (cons x2 x3))"
  theorem x0 :
    "!! (xs :: 'a list) .
       (butlast xs) = (take (minus (len xs) (S Z)) xs)"
    oops
end
