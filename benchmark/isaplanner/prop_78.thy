theory A
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
  | "sorted (cons y (cons y2 ys)) =
       (if le y y2 then sorted (cons y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (nil) = cons x (nil)"
  | "insort x (cons z xs) =
       (if le x z then cons x (cons z xs) else cons z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (nil) = nil"
  | "sort (cons y xs) = insort y (sort xs)"
  theorem x0 :
    "!! (xs :: Nat list) . sorted (sort xs)"
    oops
end
