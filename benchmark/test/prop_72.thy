theory prop_72
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
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (nil) = nil"
  | "rev (cons y xs) = append (rev xs) (cons y (nil))"
  theorem x0 :
    "!! (i :: Nat) (xs :: 'a list) .
       (rev (drop i xs)) = (take (minus (len xs) i) (rev xs))"
    oops
end
