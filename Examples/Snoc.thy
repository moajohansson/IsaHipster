theory Snoc
  imports "$HIPSTER_HOME/IsaHipster"

begin
(*setup Tactic_Data.set_sledge_induct_sledge *)
  
fun snoc :: "'a list => 'a => 'a list" 
where 
  "snoc [] a = [a]"
| "snoc (x#xs) a = x # snoc xs a"

(* Funny "feature" in QuickSpec: Seems it prunes the nessecary lemma_a if given all three functions at once!
   Probably because it decides to explore snoc and rev before snoc and append. Is the pruner too good? *)  
hipster snoc rev List.append
lemma lemma_a [thy_expl]: "snoc y z @ x2 = y @ z # x2"
  apply (induct y arbitrary: x2)
  by simp_all 
  

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
sledgehammer
  by (metis lemma_a rev.simps(2) self_append_conv)
end