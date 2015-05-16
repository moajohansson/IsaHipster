theory prop_20
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (cons2 z xs) else cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  hipster len le insort sort
  theorem x0 :
    "!! (xs :: Nat list) . (len (sort xs)) = (len xs)"
    oops
end
