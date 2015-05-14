theory prop_48
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if le x z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  theorem x0 :
    "!! (x :: Nat list) . (length (isort x)) = (length x)"
    oops
end
