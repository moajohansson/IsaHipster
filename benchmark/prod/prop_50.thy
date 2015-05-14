theory prop_50
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
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
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if equal2 x z then S (count x xs) else count x xs)"
  theorem x0 :
    "!! (x :: Nat) (y :: Nat list) . (count x (isort y)) = (count x y)"
    oops
end
