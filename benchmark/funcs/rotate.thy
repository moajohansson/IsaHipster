theory rotate
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/append"
        "../../IsaHipster"

begin

fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
| "rotate (S z) (Nil2) = Nil2"
| "rotate (S z) (Cons2 x2 x3) = rotate z (append x3 (Cons2 x2 (Nil2)))"

end

