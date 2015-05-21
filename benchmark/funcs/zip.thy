theory zip
imports Main
        "../data/list"
        "../data/Pair2"
        "../../IsaHipster"

begin

fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
| "zip (Cons2 z x2) (Nil2) = Nil2"
| "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair2 z x3) (zip x2 x4)"

end

