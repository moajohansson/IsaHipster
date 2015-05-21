theory ins
imports Main
        "../data/list"
        "../data/Natu"
        "../funcs/lt"
        "../../IsaHipster"

begin

fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (Nil2)"
| "ins x (Cons2 z xs) =
     (if lt x z then Cons2 x (Cons2 z xs) else Cons2 z (ins x xs))"

end

