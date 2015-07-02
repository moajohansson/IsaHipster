theory intersect
imports Main
        "../data/Natu"
        "../data/list"
        "../funcs/elem"
        "$HIPSTER_HOME/IsaHipster"

begin

fun intersect :: "Nat list => Nat list => Nat list" where
  "intersect (Nil2) y = Nil2"
| "intersect (Cons2 z xs) y =
     (if elem z y then Cons2 z (intersect xs y) else intersect xs y)"

hipster elem intersect equal2
lemma lemma_ad [thy_expl]: "intersect (intersect x5 y5) y5 = intersect x5 y5"
by (hipster_induct_schemes elem.simps intersect.simps equal2.simps)

lemma unknown [thy_expl]: "intersect x x = x"
oops

lemma unknown [thy_expl]: "elem x (intersect y z) = elem x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect x (intersect y z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) z = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) z = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect x (intersect x y) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect x (intersect y x) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) x = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x z) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y z) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z x) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z y) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z x) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z y) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "elem (S x) (intersect y z) = elem (S x) (intersect z y)"
oops

lemma unknown [thy_expl]: "elem Z (intersect x y) = elem Z (intersect y x)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x y) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y x) = intersect x y"
oops

lemma unknown [thy_expl]: "elem (S Z) (intersect x y) = elem (S Z) (intersect y x)"
oops


hipster_cond elem intersect equal2
lemma lemma_ae [thy_expl]: "elem x1 z1 \<Longrightarrow> elem x1 (intersect y1 z1) = elem x1 y1"
by (hipster_induct_schemes elem.simps intersect.simps equal2.simps)

lemma unknown [thy_expl]: "intersect x x = x"
oops

lemma unknown [thy_expl]: "elem x (intersect y z) = elem x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect x (intersect y z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) z = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) z = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect x (intersect x y) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect x (intersect y x) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) x = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x z) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y z) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z x) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z y) = intersect x (intersect y z)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z x) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect z y) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y z) = intersect x (intersect z y)"
oops

lemma unknown [thy_expl]: "elem (S x) (intersect y z) = elem (S x) (intersect z y)"
oops

lemma unknown [thy_expl]: "elem Z (intersect x y) = elem Z (intersect y x)"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect x y) = intersect x y"
oops

lemma unknown [thy_expl]: "intersect (intersect x y) (intersect y x) = intersect x y"
oops

lemma unknown [thy_expl]: "elem (S Z) (intersect x y) = elem (S Z) (intersect y x)"
oops

lemma unknown [thy_expl]: "elem x y \<Longrightarrow> elem x (intersect y z) = elem x z"
oops


end

