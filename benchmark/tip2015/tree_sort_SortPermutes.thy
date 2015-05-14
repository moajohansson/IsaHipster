theory tree_sort_SortPermutes
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
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if equal2 x z then S (count x xs) else count x xs)"
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
    "!! (x :: Nat) (y :: Nat list) . (count x (tsort y)) = (count x y)"
    oops
end
