theory Ltake_lmap
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
codatatype ENat = is_zero: EZ | ESuc (epred: ENat) 
primcorec ltake :: "ENat \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "is_zero n \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

(*hipster ltake lmap*)
lemma lemma_a [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
  apply (coinduction  arbitrary: y z rule: Ltake_lmap.Llist.coinduct_strong)
  by simp

lemma lemma_aa [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
apply (coinduction  arbitrary: x2 y z rule: Ltake_lmap.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "ltake y (ltake y z) = ltake y z"
apply (coinduction  arbitrary: y z rule: Ltake_lmap.Llist.coinduct_strong)
apply simp
by blast

lemma lemma_ac [thy_expl]: "ltl (ltake (ESuc y) z) = ltake y (ltl z)"
apply (coinduction  arbitrary: y z rule: Ltake_lmap.Llist.coinduct_strong)
apply simp
by (metis ENat.discI(2) ENat.sel Llist.sel(2) lnull_def ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))

lemma lemma_ad [thy_expl]: "ltake z (ltake y x2) = ltake y (ltake z x2)"
apply (coinduction  arbitrary: x2 y z rule: Ltake_lmap.Llist.coinduct_strong)
apply simp
by blast

lemma lemma_ae [thy_expl]: "ltake y (ltake (ESuc y) z) = ltake y (ltake y z)"
apply (coinduction  arbitrary: y z rule: Ltake_lmap.Llist.coinduct_strong)
apply simp
by force

lemma lemma_af [thy_expl]: "ltake (ESuc z) (LCons y x2) = LCons y (ltake z x2)"
apply (coinduction  arbitrary: x2 y z rule: Ltake_lmap.Llist.coinduct_strong)
by simp

lemma unknown [thy_expl]: "ltake (ESuc y) (ltl (ltl z)) = ltl (ltl z)"
oops 
 
theorem ltake_lmap: "ltake n (lmap f xs) = lmap f (ltake n xs)"
 (* by hipster_coinduct_sledgehammer
  Metis: Failed to replay Metis proof
resynchronize: Out of sync 
Failed to apply initial proof method
both before and after exploration
*)
  apply(coinduction arbitrary: n f xs rule: Llist.coinduct_strong)
    by (smt Llist.case_eq_if lmap.disc_iff(2) lmap.sel(1) lmap.simps(4) ltake.disc(1) ltake.disc(2) ltake.simps(3) ltake.simps(4))


end