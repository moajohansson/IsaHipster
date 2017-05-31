(* *)
theory Qrev
  imports "$HIPSTER_HOME/IsaHipster"
begin    
    


(* Hard exercise  *)
fun qrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where 
  "qrev [] acc  = acc"
| "qrev (x#xs) acc = qrev xs (x#acc)"

hipster rev qrev
lemma lemma_a [thy_expl]: "qrev (qrev z y) [] = qrev y z"
apply (induct z arbitrary: y)
apply simp
apply simp
done

lemma lemma_aa [thy_expl]: "rev y @ z = qrev y z"
apply (induct y arbitrary: z)
apply simp
apply simp
apply (metis append_eq_append_conv2 rev.simps(2) rev_append rev_singleton_conv rev_swap)
  done
    
theorem hardExercise: "rev xs = qrev xs []"
  apply (induct xs)
  apply auto  
  sledgehammer
  by (metis lemma_aa)

    
(* 
setup Tactic_Data.set_sledge_induct_sledge


lemma lemma_a [thy_expl]: "qrev (qrev z y) [] = qrev y z"
  apply (induct z arbitrary: y)
apply simp
apply simp
done

lemma lemma_aa [thy_expl]: "rev y @ z = qrev y z"
apply (induct y arbitrary: z)
apply simp
apply simp
apply (metis append_eq_append_conv2 rev.simps(2) rev_append rev_singleton_conv rev_swap)
done

lemma lemma_ab [thy_expl]: "qrev (qrev (qrev x2 z) y) x3 = qrev y (qrev (qrev z x2) x3)"
apply (metis Qrev.lemma_aa append.assoc append.right_neutral lemma_a)
done

lemma lemma_ac [thy_expl]: "qrev y [] = rev y"
apply (metis Qrev.lemma_aa append.right_neutral)
done    
*)

end