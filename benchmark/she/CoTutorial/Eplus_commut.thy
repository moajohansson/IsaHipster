theory Eplus_commut
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
  
codatatype ENat = is_zero: EZ | ESuc (epred: ENat)

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

(*hipster eplus*)
lemma lemma_a [thy_expl]: "eplus x EZ = x"
  apply (coinduction  arbitrary: x rule: Eplus_commut.ENat.coinduct_strong)
  by simp
  
lemma lemma_aa [thy_expl]: "eplus EZ x = x"
apply (coinduction  arbitrary: x rule: Eplus_commut.ENat.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "eplus (ESuc x) y = eplus x (ESuc y)"
apply (coinduction  arbitrary: x y rule: Eplus_commut.ENat.coinduct_strong)
apply simp
by (metis ENat.collapse(2) eplus.code)

lemma lemma_ac [thy_expl]: "ESuc (eplus x y) = eplus x (ESuc y)"
apply (coinduction  arbitrary: x y rule: Eplus_commut.ENat.coinduct_strong)
apply simp
by (metis eplus.code)

lemma lemma_ad [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
apply (coinduction  arbitrary: x y z rule: Eplus_commut.ENat.coinduct_strong)
apply simp
by auto

lemma lemma_ae [thy_expl]: "eplus y x = eplus x y"
apply (coinduction  arbitrary: x y rule: Eplus_commut.ENat.coinduct_strong)
apply simp
by (metis ENat.collapse(1) ENat.collapse(2) lemma_a lemma_ab)

theorem eplus_commut: "eplus a b = eplus b a"
  (*by hipster_coinduct_sledgehammer fails *)
  by (simp add: lemma_ae)

end    