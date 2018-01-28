theory Ltake_lmap
  imports Main "$HIPSTER_HOME/IsaHipster"
    Ltake
    Lmap
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

(* cohipster ltake lmap *)
(* Discovers and proves the following in ca. 40 seconds *)
lemma lemma_aj [thy_expl]: "ltake z (lmap y x2) = lmap y (ltake z x2)"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (smt ENat.collapse(2) Llist.case_eq_if Llist.sel(1) Lmap.lemma_ab Ltake.lemma_aa lmap.disc_iff(2) lmap.sel(1) ltake.ctr(2) ltake.disc(1) ltake.disc(2))
  
end