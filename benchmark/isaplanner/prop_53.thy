theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
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
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  theorem x0 :
    "!! (n :: Nat) (xs :: Nat list) .
       (count n xs) = (count n (sort xs))"
    oops
end
