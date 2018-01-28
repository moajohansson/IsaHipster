theory Lappend_append_assoc
  imports Main "$HIPSTER_HOME/IsaHipster"
    Lappend
    To_Llist
begin 
setup Tactic_Data.set_coinduct_sledgehammer 

(*cohipster lappend append to_llist*)
(*produced these lemmas and proofs in ca. 65 seconds*)
lemma lemma_af [thy_expl]: "lappend (to_llist y) (to_llist z) = to_llist (y @ z)"
  apply (induct y arbitrary: z)
  apply (simp add: lemma_aa)
  apply (simp add: lemma_ac)
  done

end