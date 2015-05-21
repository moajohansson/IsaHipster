theory union
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/elem"
        "../../IsaHipster"

begin

fun union :: "Nat list => Nat list => Nat list" where
  "union (Nil2) y = y"
| "union (Cons2 z xs) y =
     (if elem z y then union xs y else Cons2 z (union xs y))"

end

