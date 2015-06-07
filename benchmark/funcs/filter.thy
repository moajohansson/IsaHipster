theory filter
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun filtert :: "('a => bool) => 'a list => 'a list" where
  "filtert x (Nil2) = Nil2"
| "filtert x (Cons2 z xs) =
     (if x z then Cons2 z (filtert x xs) else filtert x xs)"

hipster filter

end
