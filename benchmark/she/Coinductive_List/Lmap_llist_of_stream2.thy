theory Lmap_llist_of_stream2
    imports Main "$HIPSTER_HOME/IsaHipster"
      begin
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream") 
 
primcorec llist_of_stream2 :: "'a Stream \<Rightarrow> 'a Llist"
  where "llist_of_stream2 s = LCons (shd s) (llist_of_stream2 (stl s))"
    
primcorec stream_of_llist2 :: "'a Llist \<Rightarrow> 'a Stream"
where "stream_of_llist2 l = SCons (lhd l) (stream_of_llist2 (ltl l))"   

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"
  
theorem lmap_llist_of_stream2:
  "lmap f (llist_of_stream2 xs) = llist_of_stream2 (smap f xs)"
  apply(coinduction arbitrary: f xs rule: Llist.coinduct_strong)
    by (metis (no_types, lifting) Llist.case_eq_if llist_of_stream2.disc_iff llist_of_stream2.simps(2) llist_of_stream2.simps(3) lmap.disc_iff(2) lmap.sel(1) lmap.sel(2) smap.simps(1) smap.simps(2))
(*  by hipster_coinduct_sledgehammer
    Metis: Failed to replay Metis proof
resynchronize: Out of sync 
Failed to apply initial proof method\<here>:*)
end