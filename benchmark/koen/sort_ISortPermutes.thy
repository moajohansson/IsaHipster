theory sort_ISortPermutes
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun count :: "int => int list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if x = z then S (count x xs) else count x xs)"
  hipster insert2 isort count
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (isort y)) = (count x y)"
    oops
end
