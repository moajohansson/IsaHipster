theory Ltake_lzip
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
 
datatype ('a, 'b) Pair2 = Pair2 'a 'b 

primcorec lzip :: "'a Llist \<Rightarrow> 'b Llist \<Rightarrow> (('a, 'b) Pair2) Llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (Pair2 (lhd xs) (lhd ys))"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"

codatatype ENat = is_zero: EZ | ESuc (epred: ENat) 

primcorec ltake :: "ENat \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "is_zero n \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

hipster lzip
lemma lemma_a [thy_expl]: "ltake y (ltake y z) = ltake y z"
  apply (coinduction  arbitrary: y z rule: Ltake_lzip.Llist.coinduct_strong)
  apply simp
  by blast

lemma lemma_aa [thy_expl]: "ltl (ltake (ESuc y) z) = ltake y (ltl z)"
apply (coinduction  arbitrary: y z rule: Ltake_lzip.Llist.coinduct_strong)
apply simp
by (metis ENat.discI(2) ENat.sel Llist.sel(2) lnull_def ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))

lemma lemma_ab [thy_expl]: "ltake z (ltake y x2) = ltake y (ltake z x2)"
apply (coinduction  arbitrary: x2 y z rule: Ltake_lzip.Llist.coinduct_strong)
apply simp
by blast

lemma lemma_ac [thy_expl]: "ltake y (ltake (ESuc y) z) = ltake y (ltake y z)"
apply (coinduction  arbitrary: y z rule: Ltake_lzip.Llist.coinduct_strong)
apply simp
by force

lemma lemma_ad [thy_expl]: "ltake (ESuc z) (LCons y x2) = LCons y (ltake z x2)"
apply (coinduction  arbitrary: x2 y z rule: Ltake_lzip.Llist.coinduct_strong)
by simp

lemma unknown [thy_expl]: "ltl (ltl z) = LNil"
oops

lemma unknown [thy_expl]: "ltake (ESuc y) (ltl (ltl z)) = ltl (ltl z)"
oops  
  
theorem ltake_lzip: "ltake n (lzip xs ys) = lzip (ltake n xs) (ltake n ys)"
by hipster_coinduct_sledgehammer  
end