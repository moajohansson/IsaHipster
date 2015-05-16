theory sort_ISortSorts
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (Nil2) = True"
  | "ordered (Cons2 y (Nil2)) = True"
  | "ordered (Cons2 y (cons2 y2 xs)) =
       and2 (y <= y2) (ordered (Cons2 y2 xs))"
  hipster insert2 isort and2 ordered
  theorem x0 :
    "!! (x :: int list) . ordered (isort x)"
    oops
end
