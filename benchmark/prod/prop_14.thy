theory prop_14
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (nil) = True"
  | "sorted (cons y (nil)) = True"
  | "sorted (cons y (cons y2 xs)) =
       (if le y y2 then sorted (cons y2 xs) else False)"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if le x z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  theorem x0 :
    "!! (x :: Nat list) . sorted (isort x)"
    oops
end
