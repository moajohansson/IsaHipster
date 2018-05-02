theory Lmap_lappend_distrib
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
  
primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  
(*hipster lmap lappend*)
lemma lemma_a [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
  apply (coinduction  arbitrary: y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
  by simp
    
lemma lemma_aa [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
  apply (coinduction  arbitrary: x2 y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "lappend y LNil = y"
apply (coinduction  arbitrary: y rule: Lmap_lappend_distrib.Llist.coinduct_strong)
by simp

lemma lemma_ac [thy_expl]: "lappend LNil y = y"
apply (coinduction  arbitrary: y rule: Lmap_lappend_distrib.Llist.coinduct_strong)
by simp

lemma lemma_ad [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
apply (coinduction  arbitrary: y rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (smt Llist.collapse(1) Llist.sel(2) lappend.disc_iff(2) lappend.simps(3) lappend.simps(4))

lemma lemma_ae [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
by simp

lemma lemma_af [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by blast

lemma lemma_ag [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
apply (coinduction  arbitrary: y rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (metis Llist.collapse(1) Llist.sel(2) lappend.ctr(1))

lemma lemma_ah [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
apply (coinduction  arbitrary: y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (smt Llist.case_eq_if Llist.disc(1) Llist.disc_eq_case(1) Llist.sel(1) Llist.simps(5) lmap.code ltl_def)

lemma lemma_ai [thy_expl]: "ltl (lappend z (lmap y z)) = lappend (ltl z) (lmap y z)"
apply (coinduction  arbitrary: y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (smt lappend.disc_iff(2) lappend.simps(3) lappend.simps(4) lemma_ab lmap.ctr(1) lmap.disc(2))

lemma lemma_aj [thy_expl]: "lappend (lmap y z) (lmap y x2) = lmap y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (smt Llist.case_eq_if lappend.disc_iff(2) lappend.simps(3) lappend.simps(4))

lemma lemma_ak [thy_expl]: "ltl (lappend (lmap y z) (ltl z)) = lappend (lmap y (ltl z)) (ltl z)"
apply (coinduction  arbitrary: y z rule: Lmap_lappend_distrib.Llist.coinduct_strong)
apply simp
by (smt Llist.case_eq_if Llist.collapse(2) Llist.sel(1) Llist.sel(2) lemma_aa lemma_ab lemma_ah lmap.ctr(1) lmap.disc(2) lnull_def)

lemma unknown [thy_expl]: "ltl (lappend (lmap y z) z) = lappend (lmap y (ltl z)) z"
oops

theorem  lmap_lappend_distrib: 
  "lmap f (lappend xs ys) = lappend (lmap f xs) (lmap f ys)" 
  by (simp add: lemma_aj)
  (*by hipster_coinduct_sledgehammer doesn't return anything after a long time? *)
end