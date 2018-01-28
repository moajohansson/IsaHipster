theory Lappend_literates
  imports Main "$HIPSTER_HOME/IsaHipster"
    Lappend
    Literate
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

cohipster literate lappend
lemma lemma_af [thy_expl]: "lappend (literate z x2) y = literate z x2"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    auto
(* Discovered and proved in ca. 20 seconds,
   lemmas about lappend are also discovered but discarded before proving 
   since they are already imported from Lappend.thy *)

end