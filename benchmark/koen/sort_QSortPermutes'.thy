theory sort_QSortPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun filter :: "('t => bool) => 't list => 't list" where
  "filter p (nil) = nil"
  | "filter p (cons y z) =
       (if p y then cons y (filter p z) else filter p z)"
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
  fun delete :: "int => int list => int list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if x = z then ys else cons z (delete x ys))"
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
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  theorem x0 :
    "!! (x :: int list) . isPermutation (qsort x) x"
    oops
end
