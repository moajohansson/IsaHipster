theory benchTree
imports Main
        benchNat
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a Tree = Leaf | Node "'a Tree" "'a" "'a Tree"

fun mirror :: "'a Tree => 'a Tree" where
"mirror (Leaf) = Leaf"
| "mirror (Node l y r) = Node (mirror r) y (mirror l)"

fun height :: "'a Tree => Nat" where
"height (Leaf) = Z"
| "height (Node l y r) = S (max2 (height l) (height r))"

end

