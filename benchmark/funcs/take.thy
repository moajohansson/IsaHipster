theory take
imports Main
        "../data/Natu"
        "../data/list"
        "../../IsaHipster"

begin

fun take :: "Nat => 'a list => 'a list" where
"take (Z) y = Nil2"
| "take (S z) (Nil2) = Nil2"
| "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"

(*hipster take*)

lemma lemma_ai [thy_expl]: "take x3 Nil2 = Nil2"
by (hipster_induct_simp_metis take.simps)

lemma lemma_aj [thy_expl]: "take x3 (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma lemma_ak [thy_expl]: "take (S x3) (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma unknown [thy_expl]: "take x (take y z) = take y (take x z)"
oops

lemma unknown [thy_expl]: "take (S Z) (take x y) = take (S z) (take x y)"
oops

end

