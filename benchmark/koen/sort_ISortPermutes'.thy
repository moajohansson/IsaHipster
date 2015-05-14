theory sort_ISortPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
  fun delete :: "int => int list => int list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if x = z then ys else cons z (delete x ys))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  theorem x0 :
    "!! (x :: int list) . isPermutation (isort x) x"
    oops
end
