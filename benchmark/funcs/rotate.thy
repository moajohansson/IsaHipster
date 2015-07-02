theory rotate
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/append"
        "$HIPSTER_HOME/IsaHipster"

begin

fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
| "rotate (S z) (Nil2) = Nil2"
| "rotate (S z) (Cons2 x2 x3) = rotate z (append x3 (Cons2 x2 (Nil2)))"

(*hipster rotate append*)
lemma lemma_ab [thy_expl]: "rotate x1 Nil2 = Nil2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ac [thy_expl]: "rotate x2 (Cons2 y2 Nil2) = Cons2 y2 Nil2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ad [thy_expl]: "append (rotate x3 y3) (rotate x3 y3) = rotate x3 (append y3 y3)"
by (hipster_induct_schemes rotate.simps append.simps)

lemma lemma_ae [thy_expl]: "rotate (S Z) (rotate x2 y2) = rotate (S x2) y2"
by (hipster_induct_schemes rotate.simps append.simps)

lemma unknown [thy_expl]: "rotate x (rotate y z) = rotate y (rotate x z)"
apply(induction y z arbitrary: x rule: rotate.induct)
apply(simp_all)
apply(metis thy_expl rotate.simps append.simps Nat.exhaust list.exhaust)
by (metis (no_types) lemma_ae Nat.exhaust rotate.simps append.simps list.exhaust) (* NO TYPES! hide_lams? *)

lemma unknown' [thy_expl]: "rotate (S x) (rotate y z) = rotate (S y) (rotate x z)"
by (hipster_induct_schemes rotate.simps append.simps list.exhaust Nat.exhaust)


end

