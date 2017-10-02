theory Llength_lmap
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

codatatype ENat = is_zero: EZ | ESuc (epred: ENat) 

primcorec llength :: "'a Llist \<Rightarrow> ENat" where
"llength xs = (if lnull xs then EZ else ESuc (llength (ltl xs)))" 

(*hipster llength lmap*)
lemma lemma_a [thy_expl]: "llength (LCons y z) = ESuc (llength z)"
  apply (coinduction  arbitrary: y z rule: Llength_lmap.ENat.coinduct_strong)
  by simp
  
lemma lemma_aa [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
apply (coinduction  arbitrary: y z rule: Llength_lmap.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
apply (coinduction  arbitrary: x2 y z rule: Llength_lmap.Llist.coinduct_strong)
by simp

lemma lemma_ac [thy_expl]: "llength (lmap y z) = llength z"
apply (coinduction  arbitrary: y z rule: Llength_lmap.ENat.coinduct_strong)
apply simp
by (metis Llist.case_eq_if)

lemma lemma_ad [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
apply (coinduction  arbitrary: y z rule: Llength_lmap.Llist.coinduct_strong)
apply simp
by (smt ENat.distinct(1) Llength_lmap.lemma_ab Llength_lmap.lemma_ac Llist.collapse(2) Llist.sel(1) Llist.sel(2) Llist.simps(5) llength.code lnull_def ltl_def)

theorem llength_lmap: "llength (lmap f xs) = llength xs"
  by (simp add: lemma_ac)
(*by hipster_coinduct_sledgehammer fails
Metis: Failed to replay Metis proof
resynchronize: Out of sync 
Failed to apply initial proof method *)
 (* apply(coinduction arbitrary: f xs rule: Llist.coinduct_strong)
    sledgehammer times out *)   
    
end