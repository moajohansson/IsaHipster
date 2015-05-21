theory intersect
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/elem"
        "../../IsaHipster"

begin

fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (Nil2) y = Nil2"
| "intersect (Cons2 z xs) y =
     (if elem z y then Cons2 z (intersect xs y) else intersect xs y)"

end

