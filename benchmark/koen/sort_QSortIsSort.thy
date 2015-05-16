theory sort_QSortIsSort
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
  fun filter :: "('t => bool) => 't list => 't list" where
  "filter p (Nil2) = nil2"
  | "filter p (Cons2 y z) =
       (if p y then Cons2 y (filter p z) else filter p z)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun qsort :: "int list => int list" where
  "qsort (Nil2) = nil2"
  | "qsort (Cons2 y xs) =
       append
         (append
            (qsort (filter (% (z :: int) => z <= y) xs)) (Cons2 y (Nil2)))
         (qsort (filter (% (x2 :: int) => x2 > y) xs))"
  hipster insert2 isort filter append qsort
  theorem x0 :
    "!! (x :: int list) . (qsort x) = (isort x)"
    oops
end
