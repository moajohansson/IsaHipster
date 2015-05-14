theory tree_sort_SortSorts
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (Node q z q2) y = flatten q (cons z (flatten q2 y))"
  | "flatten (Nil2) y = y"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "Nat list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (le y y2) (ordered (cons y2 xs))"
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
    "!! (x :: Nat list) . ordered (tsort x)"
    oops
end
