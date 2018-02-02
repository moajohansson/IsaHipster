theory Stream_of_llist_of_stream
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
    "types/Stream"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
primcorec llist_of_stream :: "'a Stream \<Rightarrow> 'a Llist"
  where "llist_of_stream s = LCons (shd s) (llist_of_stream (stl s))"
    
primcorec stream_of_llist :: "'a Llist \<Rightarrow> 'a Stream"
where "stream_of_llist l = SCons (lhd l) (stream_of_llist (ltl l))"   

(* cohipster stream_of_llist llist_of_stream *)
(* Discovered in about 20 seconds *)

lemma lemma_a [thy_expl]: "llist_of_stream (SCons y z) = LCons y (llist_of_stream z)"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    simp

lemma lemma_aa [thy_expl]: "stream_of_llist (llist_of_stream y) = y"
 by (coinduction arbitrary: y rule: Stream.Stream.coinduct_strong)
    simp

lemma lemma_ab [thy_expl]: "stream_of_llist (LCons y (llist_of_stream z)) = SCons y z"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_aa)  

end