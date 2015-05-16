theory sort_ISortPermutes'
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (Nil2) = True"
  | "null (Cons2 y z) = False"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun elem :: "int => int list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"
  fun delete :: "int => int list => int list" where
  "delete x (Nil2) = Nil2"
  | "delete x (Cons2 z ys) =
       (if x = z then ys else Cons2 z (delete x ys))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (Nil2) y = null y"
  | "isPermutation (Cons2 z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  hipster or2 null insert2 isort elem delete and2 isPermutation
  theorem x0 :
    "!! (x :: int list) . isPermutation (isort x) x"
    oops
end
