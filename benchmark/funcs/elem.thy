theory elem
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/equal"
        "../funcs/append"
        "$HIPSTER_HOME/IsaHipster"

begin

fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
| "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"

hipster elem equal2

hipster_cond elem append elem

hipster_cond equal2 append elem

hipster_cond elem equal2

end

