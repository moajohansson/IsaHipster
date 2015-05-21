theory drop
imports Main
        "../data/Natu"
        "../data/list"
        "../../IsaHipster"

begin

fun drop :: "Nat => 'a list => 'a list" where
"drop (Z) y = y"
| "drop (S z) (Nil2) = Nil2"
| "drop (S z) (Cons2 x2 x3) = drop z x3"

hipster drop
lemma lemma_a [thy_expl]: "drop.drop x1 Nil2 = Nil2"
by (hipster_induct_schemes drop.drop.simps)

lemma lemma_aa [thy_expl]: "drop.drop (S Z) (drop.drop x2 y2) = drop.drop (S x2) y2"
by (hipster_induct_schemes drop.drop.simps)

lemma unknown []: "drop.drop x (drop.drop y z) = drop.drop y (drop.drop x z)"
oops

lemma unknown []: "drop.drop (S x) (drop.drop y z) = drop.drop (S y) (drop.drop x z)"
oops

(* false
lemma unknown [thy_expl]: "drop.drop (S x) (drop.drop x y) = drop.drop (S x) y"
oops *)


end

