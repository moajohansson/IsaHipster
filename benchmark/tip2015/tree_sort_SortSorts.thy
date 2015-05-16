theory tree_sort_SortSorts
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun flatten :: "'a Tree => 'a list => 'a list" where
  "flatten (Node q z q2) y = flatten q (Cons2 z (flatten q2 y))"
  | "flatten (Nil2) y = y"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "Nat list => bool" where
  "ordered (Nil2) = True"
  | "ordered (Cons2 y (Nil2)) = True"
  | "ordered (Cons2 y (Cons2 y2 xs)) =
       and2 (le y y2) (ordered (Cons2 y2 xs))"
  fun add :: "Nat => Nat Tree => Nat Tree" where
  "add x (Node q z q2) =
     (if le x z then Node (add x q) z q2 else Node q z (add x q2))"
  | "add x (Nil2) = Node (Nil2) x (Nil2)"
  fun toTree :: "Nat list => Nat Tree" where
  "toTree (Nil2) = Nil2"
  | "toTree (Cons2 y xs) = add y (toTree xs)"
  fun tsort :: "Nat list => Nat list" where
  "tsort x = flatten (toTree x) (Nil2)"
  hipster le flatten and2 ordered add toTree tsort
  theorem x0 :
    "!! (x :: Nat list) . ordered (tsort x)"
    oops
end
