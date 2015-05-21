theory sorted
imports Main
        "../data/list"
        "../funcs/le"
        "../../IsaHipster"

begin

fun sorted :: "Nat list => bool" where
  "sorted (Nil2) = True"
| "sorted (Cons2 y (Nil2)) = True"
| "sorted (Cons2 y (Cons2 y2 ys)) =
     (if le y y2 then sorted (Cons2 y2 ys) else False)"

end

