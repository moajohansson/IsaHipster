theory zipConcat
imports Main
        "../data/list"
        "../data/Pair2"
        "../../IsaHipster"

begin

fun zipConcat :: "'a => 'a list => 'b list => (('a, 'b) Pair2) list" where
  "zipConcat x y (Nil2) = Nil2"
| "zipConcat x y (Cons2 y2 ys) = Cons2 (Pair x y2) (zip y ys)"

end

