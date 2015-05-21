theory rev
imports Main
        "../data/list"
        "../funcs/append"
        "../../IsaHipster"

begin

fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
| "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"

end

