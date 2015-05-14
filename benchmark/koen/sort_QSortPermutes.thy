theory sort_QSortPermutes
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun filter :: "('t => bool) => 't list => 't list" where
  "filter q (nil) = nil"
  | "filter q (cons y z) =
       (if q y then cons y (filter q z) else filter q z)"
  fun count :: "int => int list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if x = z then S (count x xs) else count x xs)"
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
    "!! (x :: int) (y :: int list) . (count x (qsort y)) = (count x y)"
    oops
end
