theory prop_08
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
lemma lemma_a [thy_expl]: "drop x3 Nil2 = Nil2"
by (hipster_induct_schemes drop.simps)

lemma lemma_aa [thy_expl]: "drop (S Z) (drop x3 y3) = drop (S x3) y3"
by (hipster_induct_schemes drop.simps)

lemma lemma_ab []: "drop (S z) (drop x3 y3) = drop z (drop (S x3) y3)"
by (metis thy_expl drop.simps list.exhaust)

  theorem x0 :
    "(drop x (drop y z)) = (drop y (drop x z))"
    by (hipster_induct_schemes drop.simps list.exhaust)
    
end
