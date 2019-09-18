(* *)
theory Qrev
  imports "$HIPSTER_HOME/IsaHipster"
begin    
    
(*setup Tactic_Data.set_sledge_induct_sledge*)


(* Hard exercise  *)
fun qrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where 
  "qrev [] acc  = acc"
| "qrev (x#xs) acc = qrev xs (x#acc)"



hipster rev qrev
lemma lemma_a [thy_expl]: "rev y @ z = qrev y z"
  apply (induct y arbitrary: z)
  apply simp
  apply (metis append.assoc append_Cons append_eq_append_conv2 append_self_conv qrev.simps(2) rev.simps(2))
  done
    
lemma lemma_aa [thy_expl]: "x2 @ z @ [y] = rev (y # qrev z (rev x2))"
  apply (induct x2 arbitrary: z)
  apply (metis append_Nil2 lemma_a rev.simps(1) rev.simps(2) rev_rev_ident self_append_conv2)
  apply (metis (no_types, lifting) append_Cons lemma_a rev.simps(2) rev_append rev_eq_Cons_iff rev_singleton_conv)
  done


  theorem hardExercise: "rev xs = qrev xs Nil"
  sledgehammer
  by (metis append_Nil2 lemma_a)
end