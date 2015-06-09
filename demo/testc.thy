theory testc
imports Main
        "../IsaHipster"
begin

datatype Nat = Z | S Nat

fun le :: "Nat => Nat => bool" where
  "le Z      y      = True"
| "le (S z) (S x2)  = le z x2"

thm le.induct
fun eqN :: "Nat => Nat => bool" where
  "eqN Z      Z    = True"
| "eqN Z     (S z) = False"
| "eqN (S x)  Z    = False"
| "eqN (S x) (S y) = eqN x y"

setup{*Hip_Tac_Ops.toggle_full_types @{context}*}
setup{*Hip_Tac_Ops.set_metis_to @{context} 1000*}

hipster_cond le
lemma lemma_a [thy_expl]: "le x2 x2 = True"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_aa [thy_expl]: "le x2 (S x2) = True"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_ab [thy_expl]: "le (S x2) x2 = False"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_ac [thy_expl]: "le x9 y9 \<Longrightarrow> le x9 (S y9) = True"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_ad [thy_expl]: "le y10 x10 \<Longrightarrow> le (S x10) y10 = False"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_ae [thy_expl]: "le y10 x10 \<and> le x10 y10 \<Longrightarrow> x10 = y10"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

lemma lemma_af [thy_expl]: "le z10 y10 \<and> le x10 z10 \<Longrightarrow> le x10 y10 = True"
by (hipster_induct_schemes testc.le.simps testc.Nat.exhaust)

end
