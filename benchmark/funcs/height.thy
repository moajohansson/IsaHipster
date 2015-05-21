theory mirror
imports Main
        "../data/Tree"
        "../funcs/max"
        "../../IsaHipster"

begin

fun height :: "'a Tree => Nat" where
  "height (Leaf) = Z"
| "height (Node l y r) = S (max2 (height l) (height r))"

end

