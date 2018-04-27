theory LtakeWhile_lmap
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
primcorec ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "lnull xs \<or> \<not> P (lhd xs) \<Longrightarrow> lnull (ltakeWhile P xs)"
| "lhd (ltakeWhile P xs) = lhd xs"
| "ltl (ltakeWhile P xs) = ltakeWhile P (ltl xs)"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

hipster lmap ltakeWhile
lemma lemma_a [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
  apply (coinduction  arbitrary: y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
  by simp
    
lemma lemma_aa [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
  apply (coinduction  arbitrary: x2 y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "ltakeWhile y (ltakeWhile y z) = ltakeWhile y z"
apply (coinduction  arbitrary: y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
apply simp
by fastforce

lemma lemma_ac [thy_expl]: "ltakeWhile z (ltakeWhile y x2) = ltakeWhile y (ltakeWhile z x2)"
apply (coinduction  arbitrary: x2 y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
apply simp
by fastforce

lemma lemma_ad [thy_expl]: "ltakeWhile y (ltl (ltakeWhile y z)) = ltl (ltakeWhile y z)"
apply (coinduction  arbitrary: y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
apply simp
by (metis (mono_tags, lifting) Llist.sel(2) lemma_ab lnull_def ltakeWhile.ctr(1) ltakeWhile.simps(4))

lemma lemma_ae [thy_expl]: "ltakeWhile y (LCons z (ltakeWhile y x2)) = ltakeWhile y (LCons z x2)"
apply (coinduction  arbitrary: x2 y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
by (simp_all add: lemma_ab)

lemma lemma_af [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
apply (coinduction  arbitrary: y z rule: LtakeWhile_lmap.Llist.coinduct_strong)
apply simp
by (smt Llist.collapse(2) Llist.disc_eq_case(1) Llist.sel(1) Llist.sel(2) Llist.sel(3) Llist.simps(5) lmap.code lmap.ctr(1) lnull_def)

lemma unknown [thy_expl]: "ltl (ltl (ltakeWhile y z)) = ltl (ltakeWhile y (ltl z))"
oops 
 
lemma ltakeWhile_lmap: "ltakeWhile P (lmap f xs) = lmap f (ltakeWhile (P \<circ> f) xs)"
  apply(coinduction arbitrary: P f xs rule: Llist.coinduct_strong)
  by (smt Llist.case_eq_if Llist.sel(1) comp_apply lemma_af lmap.disc_iff(2) lmap.sel(1) ltakeWhile.ctr(2) ltakeWhile.disc_iff(2) ltakeWhile.simps(4))
 (* also works:
apply(coinduction arbitrary: P f xs rule: Llist.coinduct_strong)
    by (smt Llist.case_eq_if comp_apply lmap.disc_iff(2) lmap.sel(1) lmap.sel(2) ltakeWhile.disc(1) ltakeWhile.disc(2) ltakeWhile.simps(3) ltakeWhile.simps(4))
 but hipster_coinduct_sledgehammer just kept running with no results  *) 
end