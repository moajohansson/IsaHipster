theory height
imports Main
        "../data/Tree"
        "../data/Natu"
        "../funcs/max"
        "../../IsaHipster"

begin

fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
| "height (Node l y r) = S (max2 (height l) (height r))"

end

