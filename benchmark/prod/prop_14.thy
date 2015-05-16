theory prop_14
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
  | "sorted (Cons2 y (cons2 y2 xs)) =
       (if le y y2 then sorted (Cons2 y2 xs) else False)"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun isort :: "Nat list => Nat list" where
  "isort (Nil2) = nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  hipster le sorted insert2 isort
  theorem x0 :
    "!! (x :: Nat list) . sorted (isort x)"
    oops
end
