theory sort_QSortIsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun filter :: "('t => bool) => 't list => 't list" where
  "filter p (nil) = nil"
  | "filter p (cons y z) =
       (if p y then cons y (filter p z) else filter p z)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun qsort :: "int list => int list" where
  "qsort (nil) = nil"
  | "qsort (cons y xs) =
       append
         (append
            (qsort (filter (% (z :: int) => z <= y) xs)) (cons y (nil)))
         (qsort (filter (% (x2 :: int) => x2 > y) xs))"
  theorem x0 :
    "!! (x :: int list) . (qsort x) = (isort x)"
    oops
end
