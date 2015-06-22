theory prop_47
imports Main
begin
  datatype 'a Tree = Leaf | Node "'a Tree" "'a" "'a Tree"
  datatype Nat = Z | S "Nat"
  fun mirror :: "'a Tree => 'a Tree" where
  "mirror (Leaf) = Leaf"
  | "mirror (Node l y r) = Node (mirror r) y (mirror l)"
  fun max2 :: "Nat => Nat => Nat" where
  "max2 (Z) y = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
  | "height (Node l y r) = S (max2 (height l) (height r))"
  theorem x0 :
    "!! (b :: 'a Tree) . (height (mirror b)) = (height b)"
    oops
end
