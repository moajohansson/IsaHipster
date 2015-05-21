theory drop
imports Main
        "../data/Nat"
        "../data/list"
        "../../IsaHipster"

begin

fun drop :: "Nat => 'a list => 'a list" where
"drop (Z) y = y"
| "drop (S z) (Nil2) = Nil2"
| "drop (S z) (Cons2 x2 x3) = drop z x3"

lemma lemma_a [thy_expl]: "drop x3 Nil2 = Nil2"
by (hipster_induct_schemes drop.simps)

lemma lemma_aa [thy_expl]: "drop (S Z) (drop x3 y3) = drop (S x3) y3"
by (hipster_induct_schemes drop.simps)

lemma unknown [thy_expl]: "drop x (drop y z) = drop y (drop x z)"
oops

lemma unknown [thy_expl]: "drop (S x) (drop y z) =
drop (S y) (drop x z)"
oops

end

