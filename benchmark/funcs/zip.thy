theory zip
imports Main
        "../data/list"
        "../data/Pair2"
        "$HIPSTER_HOME/IsaHipster"

begin

fun zip2 :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip2 (Nil2) y = Nil2"
| "zip2 (Cons2 z x2) (Nil2) = Nil2"
| "zip2 (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair2 z x3) (zip2 x2 x4)"

(*hipster zip2*)
lemma lemma_a [thy_expl]: "zip2 Nil2 x1 = zip2 x1 Nil2"
by (hipster_induct_schemes zip2.simps)

lemma lemma_aa [thy_expl]: "zip2 Nil2 x1 = zip2 y1 Nil2"
by (hipster_induct_schemes zip2.simps)

end

