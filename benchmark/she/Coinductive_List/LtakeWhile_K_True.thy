theory LtakeWhile_K_True
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
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
(*hipster ltakeWhile *)
lemma lemma_a [thy_expl]: "ltakeWhile y (ltakeWhile y z) = ltakeWhile y z"
apply (coinduction  arbitrary: y z rule: LtakeWhile_K_True.Llist.coinduct_strong)
  apply simp
by fastforce

lemma lemma_aa [thy_expl]: "ltakeWhile z (ltakeWhile y x2) = ltakeWhile y (ltakeWhile z x2)"
apply (coinduction  arbitrary: x2 y z rule: LtakeWhile_K_True.Llist.coinduct_strong)
apply simp
by fastforce

lemma lemma_ab [thy_expl]: "ltakeWhile y (ltl (ltakeWhile y z)) = ltl (ltakeWhile y z)"
apply (coinduction  arbitrary: y z rule: LtakeWhile_K_True.Llist.coinduct_strong)
apply simp
by (metis (mono_tags, lifting) Llist.sel(2) lemma_a lnull_def ltakeWhile.ctr(1) ltakeWhile.simps(4))

lemma lemma_ac [thy_expl]: "ltakeWhile y (LCons z (ltakeWhile y x2)) = ltakeWhile y (LCons z x2)"
apply (coinduction  arbitrary: x2 y z rule: LtakeWhile_K_True.Llist.coinduct_strong)
apply simp
by (auto lemma_a)

lemma unknown [thy_expl]: "ltl (ltl (ltl y)) = LNil"
oops  
theorem ltakeWhile_K_True: "ltakeWhile (\<lambda>_. True) xs = xs"
  by hipster_coinduct_sledgehammer
end