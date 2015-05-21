theory lastOfTwo
imports Main
        "../data/Nat"
        "../data/list"
        "../funcs/last"
        "../../IsaHipster"

begin

fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
| "lastOfTwo x (Cons2 z x2) = last (Cons2 z x2)"

lemma lemma_a [thy_expl]: "last x2 = lastOfTwo x2 x2"
by (hipster_induct_schemes lastOfTwo.simps)

hipster append last
lemma lemma_aa [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps last.simps)

lemma lemma_ab [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes append.simps last.simps)

end

