theory Llength
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
    "types/ENat"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

primcorec llength :: "'a Llist \<Rightarrow> ENat" where
"llength xs = (if lnull xs then EZ else ESuc (llength (ltl xs)))" 

(* cohipster llength *)
(* Found and proved in ca. 5 seconds *)
lemma lemma_a [thy_expl]: "llength (LCons y z) = ESuc (llength z)"
  by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
    simp

end