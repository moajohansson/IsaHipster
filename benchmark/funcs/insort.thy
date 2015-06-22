theory insort
imports Main
        "../data/list"
        "../funcs/le"
        "../../IsaHipster"

begin

fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
| "insort x (Cons2 z xs) =
     (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"

end

