theory sort_QSortPermutes
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun filter :: "('t => bool) => 't list => 't list" where
  "filter q (Nil2) = nil2"
  | "filter q (Cons2 y z) =
       (if q y then Cons2 y (filter q z) else filter q z)"
  fun count :: "int => int list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if x = z then S (count x xs) else count x xs)"
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
  hipster filter count append qsort
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (qsort y)) = (count x y)"
    oops
end
