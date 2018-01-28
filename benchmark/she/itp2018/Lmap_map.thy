theory Lmap_map
  imports Main "$HIPSTER_HOME/IsaHipster"
    "Lmap"
    "To_Llist"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

(* cohipster lmap map to_llist *)
(* Found and proved in ca. 70 seconds *)
lemma lemma_ac [thy_expl]: "to_llist (map y z) = lmap y (to_llist z)"
  apply (induct z)
apply (simp add: lmap.ctr(1))
apply (simp add: lemma_aa)
done

end