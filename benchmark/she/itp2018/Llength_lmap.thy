theory Llength_lmap
  imports Main "$HIPSTER_HOME/IsaHipster"
    "Llength"
    "Lmap"

begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

cohipster llength lmap
(* Discovers and proves the following in ca. 20 seconds *)
lemma lemma_ac [thy_expl]: "llength (lmap y z) = llength z"
  by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
    (metis lemma_ab llength.disc_iff(1) llength.sel lmap.disc_iff(2))


end