theory rev
imports Main
        "../data/list"
        "../funcs/append"
        "$HIPSTER_HOME/IsaHipster"

begin

fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
| "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"

hipster rev append
lemma lemma_ab [thy_expl]: "append (rev x4) (rev y4) = rev (append y4 x4)"
by (hipster_induct_schemes rev.simps append.simps)

lemma lemma_ac [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes rev.simps append.simps)


end

