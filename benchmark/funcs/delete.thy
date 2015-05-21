theory delete
imports Main
        "../data/list"
        "../data/Nat"
        "../funcs/equal"
        "../../IsaHipster"

begin

fun delete :: "Nat => Nat list => Nat list" where
  "delete x (Nil2) = Nil2"
| "delete x (Cons2 z xs) =
     (if equal2 x z then delete x xs else Cons2 z (delete x xs))"

end
