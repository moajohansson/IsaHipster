theory subset
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/elem"
        "../../IsaHipster"

begin

fun subset :: "Nat list => Nat list => bool" where
  "subset (Nil2) y = True"
| "subset (Cons2 z xs) y =
     (if elem z y then subset xs y else False)"

end

