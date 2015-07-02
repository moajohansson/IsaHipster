theory sort
imports Main
        "../data/list"
        "../funcs/insort"
        "$HIPSTER_HOME/IsaHipster"

begin

fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
| "sort (Cons2 y xs) = insort y (sort xs)"

end

