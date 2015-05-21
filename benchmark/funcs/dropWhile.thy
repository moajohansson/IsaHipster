theory dropWhile
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (Nil2) = Nil2"
| "dropWhile x (Cons2 z xs) =
     (if x z then dropWhile x xs else Cons2 z xs)"

end
