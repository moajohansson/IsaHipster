theory Lmap_lappend
  imports Main "$HIPSTER_HOME/IsaHipster"
    "Lappend"
    "Lmap"

begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

(* cohipster lmap lappend *)
(* Discovers and proves the following in ca. 80 seconds *)
lemma lemma_af [thy_expl]: "ltl (lappend z (lmap y z)) = lappend (ltl z) (lmap y z)"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
  (metis Lappend.lemma_a lappend.simps(4) lmap.ctr(1))
  
lemma lemma_ag [thy_expl]: "ltl (lappend (lmap y z) z) = lappend (lmap y (ltl z)) z"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.sel(2) Lmap.lemma_ab lappend.disc_iff(1) lappend.simps(4) lmap.disc_iff(2) lnull_def)
    
lemma lemma_ah [thy_expl]: "ltl (lappend (lmap y z) (ltl z)) = lappend (lmap y (ltl z)) (ltl z)"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.sel(2) Lmap.lemma_ab lappend.ctr(1) lappend.simps(4) lmap.disc_iff(2) lnull_def)
(* lmap distributes over lappend *)    
lemma lemma_ai [thy_expl]: "lappend (lmap y z) (lmap y x2) = lmap y (lappend z x2)"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.case_eq_if Lmap.lemma_ab lappend.disc_iff(1) lappend.simps(3) lappend.simps(4) lmap.disc_iff(2) lmap.sel(1))


  
end