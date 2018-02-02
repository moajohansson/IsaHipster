theory Pls_ac_enat
  imports Main  "~~/src/HOL/Library/BNF_Corec" "$HIPSTER_HOME/IsaHipster" 
begin    
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

codatatype ENat = is_zero: EZ | ESuc (epred: ENat)

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

primcorec pls :: "ENat Stream \<Rightarrow> ENat Stream \<Rightarrow> ENat Stream" where
  "pls s t = SCons (eplus (shd s) (shd t)) (pls (stl s) (stl t))"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream pls*)
lemma lemma_a [thy_expl]: "eplus x EZ = x"
  apply (coinduction  arbitrary: x rule: Pls_ac_enat.ENat.coinduct_strong)
  by simp

lemma lemma_aa [thy_expl]: "eplus EZ x = x"
  apply (coinduction  arbitrary: x rule: Pls_ac_enat.ENat.coinduct_strong)
  by simp
    
lemma lemma_ab [thy_expl]: "eplus (ESuc x) y = eplus x (ESuc y)"
  apply (coinduction  arbitrary: x y rule: Pls_ac_enat.ENat.coinduct_strong)
  apply simp
  by (metis ENat.collapse(2) eplus.code)
    
lemma lemma_ac [thy_expl]: "ESuc (eplus x y) = eplus x (ESuc y)"
  apply (coinduction  arbitrary: x y rule: Pls_ac_enat.ENat.coinduct_strong)
  apply simp
  by (metis eplus.code)
    
lemma lemma_ad [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
  apply (coinduction  arbitrary: x y z rule: Pls_ac_enat.ENat.coinduct_strong)
  apply simp
  by blast
    
lemma lemma_ae [thy_expl]: "eplus y x = eplus x y"
  apply (coinduction  arbitrary: x y rule: Pls_ac_enat.ENat.coinduct_strong)
  apply simp
  by (metis ENat.collapse(1) ENat.collapse(2) lemma_a lemma_ab)

lemma pls_ac: "pls s (pls t u) = pls t (pls s u)"
  by hipster_coinduct_sledgehammer
  (*by hipster_coinduct_sledgehammer
Failed to apply initial proof method\<here>:*)
end   