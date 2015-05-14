theory sort_QSortSorts
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
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
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (y <= y2) (ordered (cons y2 xs))"
  theorem x0 :
    "!! (x :: int list) . ordered (qsort x)"
    oops
end
