theory tree_sort_SortPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  datatype Nat = Z | S "Nat"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'a list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (Node q z q2) y = flatten q (cons z (flatten q2 y))"
  | "flatten (Nil2) y = y"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (equal2 x z) (elem x ys)"
  fun delete :: "Nat => Nat list => Nat list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if equal2 x z then ys else cons z (delete x ys))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "Nat list => Nat list => bool" where
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  fun add :: "Nat => Nat Tree => Nat Tree" where
  "add x (Node q z q2) =
     (if le x z then Node (add x q) z q2 else Node q z (add x q2))"
  | "add x (Nil2) = Node (Nil2) x (Nil2)"
  fun toTree :: "Nat list => Nat Tree" where
  "toTree (nil) = Nil2"
  | "toTree (cons y xs) = add y (toTree xs)"
  fun tsort :: "Nat list => Nat list" where
  "tsort x = flatten (toTree x) (nil)"
  theorem x0 :
    "!! (x :: Nat list) . isPermutation (tsort x) x"
    oops
end
