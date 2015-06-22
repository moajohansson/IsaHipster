theory prop_09
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster drop *)

(*hipster drop*)
lemma lemma_a [thy_expl]: "drop x1 Nil2 = Nil2"
by (hipster_induct_schemes drop.simps)

lemma lemma_aa [thy_expl]: "drop (S Z) (drop x2 y2) = drop (S x2) y2"
by (hipster_induct_schemes drop.simps)

lemma lemma_ab [thy_expl]: "drop x (drop y z) = drop y (drop x z)"
by (hipster_induct_schemes drop.simps  list.exhaust)

lemma lemma_ac [thy_expl]: "drop (S x) (drop y z) = drop (S y) (drop x z)"
by (hipster_induct_schemes drop.simps  list.exhaust)


  theorem x0 :
    "(drop w (drop x (drop y z))) = (drop y (drop x (drop w z)))"
    by (hipster_induct_schemes drop.simps  list.exhaust)

end
