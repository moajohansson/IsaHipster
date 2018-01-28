theory Ltake
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
    "types/ENat"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

primcorec ltake :: "ENat \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "is_zero n \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

(* cohipster ltake *)
(* Discovers and proves the following in ca. 70 seconds *)
lemma lemma_a [thy_expl]: "ltake y (ltake y z) = ltake y z"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    auto

lemma lemma_aa [thy_expl]: "ltl (ltake (ESuc y) z) = ltake y (ltl z)"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (metis ENat.discI(2) ENat.sel Llist.sel(2) lnull_def ltake.ctr(1) ltake.simps(4))

lemma lemma_ab [thy_expl]: "ltake z (ltake y x2) = ltake y (ltake z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    auto

lemma lemma_ac [thy_expl]: "ltake y (ltake (ESuc y) z) = ltake y z"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt ENat.collapse(2) ENat.discI(2) lemma_aa ltake.disc(1) ltake.disc(2) ltake.simps(3))

lemma lemma_ad [thy_expl]: "ltake y (ltl (ltake y z)) = ltl (ltake y z)"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.sel(2) ltake.ctr(1) ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))

lemma lemma_ae [thy_expl]: "ltake (ESuc z) (LCons y x2) = LCons y (ltake z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    simp

lemma lemma_af [thy_expl]: "ltake y (LCons z (ltake y x2)) = ltake y (LCons z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.disc(2) Llist.sel(1) Llist.sel(3) Ltake.lemma_ad lemma_ab ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))

lemma lemma_ag [thy_expl]: "ltake (ESuc y) (ltl (ltake y z)) = ltl (ltake y z)"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (metis lemma_aa lemma_ad)

lemma lemma_ah [thy_expl]: "ltake (ESuc (ESuc y)) (ltake y z) = ltake y z"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (metis ENat.discI(2) lemma_aa lemma_ag ltake.disc_iff(2) ltake.simps(3))

lemma lemma_ai [thy_expl]: "ltake (ESuc EZ) (ltake (ESuc y) z) = ltake (ESuc EZ) z"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (simp add: ltake.ctr(1))  
end