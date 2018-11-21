theory Snoc
  imports "$HIPSTER_HOME/IsaHipster"

begin
  
fun snoc :: "'a list => 'a => 'a list" 
where 
  "snoc [] a = [a]"
| "snoc (x#xs) a = x # snoc xs a"

hipster snoc rev List.append
lemma lemma_a [thy_expl]: "rev (snoc z y) = y # rev z"
  apply (induct z)
  apply simp
  apply auto
  done

end
  
  
  
  
  
  (* Funny "feature" in QuickSpec: Seems it prunes the nessecary lemma_a if given all three functions at once!
   Probably because it decides to explore snoc and rev before snoc and append. Is the pruner too good? *)  
