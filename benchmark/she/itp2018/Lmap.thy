theory Lmap
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

(*cohipster lmap lhd ltl*)
(* Discovered and proved in ca. 20 seconds*)
lemma lemma_a [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
  simp
  
lemma lemma_aa [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    simp

lemma lemma_ab [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.case_eq_if Llist.collapse(2) Llist.inject lemma_aa lmap.disc_iff(2) lnull_def ltl_def)



end