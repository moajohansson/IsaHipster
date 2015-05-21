theory append
imports Main
        "../data/list"
        "../../IsaHipster"

begin

fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

(*hipster append*)

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes  append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 =
append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps)

end

