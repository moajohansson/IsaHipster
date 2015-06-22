theory dropWhile
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun dropWhilet :: "('a => bool) => 'a list => 'a list" where
  "dropWhilet x (Nil2) = Nil2"
| "dropWhilet x (Cons2 z xs) =
     (if x z then dropWhilet x xs else Cons2 z xs)"

hipster dropWhilet
lemma lemma_a [thy_expl]: "dropWhilet x5 (dropWhilet x5 y5) = dropWhilet x5 y5"
by (hipster_induct_schemes dropWhilet.simps)

end
