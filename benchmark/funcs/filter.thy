theory filter
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter x (Nil2) = Nil2"
| "filter x (Cons2 z xs) =
     (if x z then Cons2 z (filter x xs) else filter x xs)"

end
