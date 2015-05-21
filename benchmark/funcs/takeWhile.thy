theory takeWhile
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (Nil2) = Nil2"
| "takeWhile x (Cons2 z xs) =
     (if x z then Cons2 z (takeWhile x xs) else Nil2)"

end
