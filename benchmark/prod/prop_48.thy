theory prop_48
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun length :: "'a list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  hipster length le insert2 isort
  theorem x0 :
    "!! (x :: Nat list) . (length (isort x)) = (length x)"
    oops
end
