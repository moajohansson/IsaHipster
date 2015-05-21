theory last
imports Main
        "../data/Natu"
        "../data/list"
        "../../IsaHipster"

begin

fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
| "last (Cons2 y (Nil2)) = y"
| "last (Cons2 y (Cons2 x2 x3)) = last (Cons2 x2 x3)"

end

