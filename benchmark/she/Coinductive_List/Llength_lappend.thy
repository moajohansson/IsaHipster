theory Llength_lappend
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

codatatype ENat = is_zero: EZ | ESuc (epred: ENat) 

primcorec llength :: "'a Llist \<Rightarrow> ENat" where
"llength xs = (if lnull xs then EZ else ESuc (llength (ltl xs)))" 

primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

(*hipster llength lappend eplus*)
lemma lemma_a [thy_expl]: "eplus x EZ = x"
  apply (coinduction  arbitrary: x rule: Llength_lappend.ENat.coinduct_strong)
  by simp
    
lemma lemma_aa [thy_expl]: "eplus EZ x = x"
apply (coinduction  arbitrary: x rule: Llength_lappend.ENat.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "eplus (ESuc x) y = eplus x (ESuc y)"
apply (coinduction  arbitrary: x y rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by (metis ENat.collapse(2) eplus.code)

lemma lemma_ac [thy_expl]: "ESuc (eplus x y) = eplus x (ESuc y)"
apply (coinduction  arbitrary: x y rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by (metis eplus.code)

lemma lemma_ad [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
apply (coinduction  arbitrary: x y z rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by auto

lemma lemma_ae [thy_expl]: "llength (LCons y z) = ESuc (llength z)"
apply (coinduction  arbitrary: y z rule: Llength_lappend.ENat.coinduct_strong)
by simp

lemma lemma_af [thy_expl]: "lappend y LNil = y"
apply (coinduction  arbitrary: y rule: Llength_lappend.Llist.coinduct_strong)
by simp

lemma lemma_ag [thy_expl]: "lappend LNil y = y"
apply (coinduction  arbitrary: y rule: Llength_lappend.Llist.coinduct_strong)
by simp

lemma lemma_ah [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
apply (coinduction  arbitrary: y rule: Llength_lappend.Llist.coinduct_strong)
apply simp
by (smt Llist.collapse(1) Llist.sel(2) lappend.disc_iff(2) lappend.simps(3) lappend.simps(4))

lemma lemma_ai [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Llength_lappend.Llist.coinduct_strong)
by simp

lemma lemma_aj [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Llength_lappend.Llist.coinduct_strong)
apply simp
by blast

lemma lemma_ak [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
apply (coinduction  arbitrary: y rule: Llength_lappend.Llist.coinduct_strong)
apply simp
by (fastforce Llist.collapse(1) lemma_af)

lemma lemma_al [thy_expl]: "eplus (llength y) (llength z) = llength (lappend y z)"
apply (coinduction  arbitrary: y z rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by auto

lemma lemma_am [thy_expl]: "eplus y x = eplus x y"
apply (coinduction  arbitrary: x y rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by (metis ENat.collapse(1) ENat.collapse(2) lemma_a lemma_ab)

lemma lemma_an [thy_expl]: "llength (lappend z y) = llength (lappend y z)"
apply (coinduction  arbitrary: y z rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by (metis (no_types, lifting) Llength_lappend.lemma_af Llength_lappend.lemma_al Llist.collapse(1) lemma_ab llength.code)

lemma lemma_ao [thy_expl]: "llength (ltl (lappend z y)) = llength (ltl (lappend y z))"
apply (coinduction  arbitrary: y z rule: Llength_lappend.ENat.coinduct_strong)
apply simp
by (smt Llist.case_eq_if lemma_an llength.disc_iff(1) llength.sel ltl_def)
    
theorem  llength_lappend: "llength (lappend xs ys) = eplus (llength xs) (llength ys)"
by hipster_coinduct_sledgehammer
end