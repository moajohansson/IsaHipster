theory equal
imports Main
        "../data/Natu"
        "$HIPSTER_HOME/IsaHipster"
begin

fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

(*hipster equal2*)
lemma lemma_a [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa [thy_expl]: "equal2 x2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aa' : "y = x2 \<Longrightarrow> equal2 x2 y"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ab [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster_cond equal2*)

lemma lemma_ac [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps)

end

