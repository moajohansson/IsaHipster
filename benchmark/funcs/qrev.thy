theory qrev
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (Nil2) y = y"
| "qrev (Cons2 z xs) y = qrev xs (Cons2 z y)"

end

