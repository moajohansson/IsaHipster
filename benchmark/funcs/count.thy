theory count
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/equal"
        "../../IsaHipster"

begin

fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
| "count x (Cons2 z ys) =
     (if equal2 x z then S (count x ys) else count x ys)"

end

