theory insert2
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/le"
        "$HIPSTER_HOME/IsaHipster"

begin

fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
| "insert2 x (Cons2 z xs) =
     (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"

end

