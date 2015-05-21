theory ins1
imports Main
        "../data/Nat"
        "../data/list"
        "../function/le"
        "../../IsaHipster"

begin

fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
| "insert2 x (Cons2 z xs) =
     (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"

end

