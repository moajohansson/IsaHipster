theory lastOfTwo
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/last"
        "../funcs/append"
        "../../IsaHipster"

begin

fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
| "lastOfTwo x (Cons2 z x2) = last (Cons2 z x2)"

lemma lemma_a [thy_expl]: "last x2 = lastOfTwo x2 x2"
by (hipster_induct_schemes lastOfTwo.simps)

(*hipster append last*)

end

