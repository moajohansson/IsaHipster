theory elem
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/equal"
        "../../IsaHipster"

begin

fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
| "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"

end

