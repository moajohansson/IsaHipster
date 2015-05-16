theory prop_78
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
  | "sorted (Cons2 y (Nil2)) = True"
  | "sorted (Cons2 y (cons2 y2 ys)) =
       (if le y y2 then sorted (Cons2 y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (cons2 z xs) else cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  hipster le sorted insort sort
  theorem x0 :
    "!! (xs :: Nat list) . sorted (sort xs)"
    oops
end
