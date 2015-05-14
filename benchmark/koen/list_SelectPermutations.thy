theory list_SelectPermutations
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun select2 :: "'a => (('a, ('a list)) Pair2) list =>
                  (('a, ('a list)) Pair2) list" where
  "select2 x (nil) = nil"
  | "select2 x (cons (Pair y2 ys) x2) =
       cons (Pair y2 (cons x ys)) (select2 x x2)"
  fun select :: "'a list => (('a, ('a list)) Pair2) list" where
  "select (nil) = nil"
  | "select (cons y xs) = cons (Pair y xs) (select2 y (select xs))"
  fun propSelectPermutations :: "((int, (int list)) Pair2) list =>
                                 (int list) list" where
  "propSelectPermutations (nil) = nil"
  | "propSelectPermutations (cons (Pair y2 ys) z) =
       cons (cons y2 ys) (propSelectPermutations z)"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
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
  fun all :: "('t => bool) => 't list => bool" where
  "all x (nil) = True"
  | "all x (cons z xs) = and2 (x z) (all x xs)"
  theorem x0 :
    "!! (xs :: int list) .
       all
         (% (x :: int list) => isPermutation x xs)
         (propSelectPermutations (select xs))"
    oops
end
