theory sort_ISortSorts
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
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (y <= y2) (ordered (cons y2 xs))"
  theorem x0 :
    "!! (x :: int list) . ordered (isort x)"
    oops
end
