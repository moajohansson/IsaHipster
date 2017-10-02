theory Llist_of_stream_siterates2
    imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
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

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "shd (siterate f x) = x"
| "stl (siterate f x) = siterate f (f x)"      

primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literates f x = LCons x (literates f (f x))"

theorem llist_of_stream_siterates2: 
"llist_of_stream2 (siterate f x) = literates f x"
  by hipster_coinduct_sledgehammer

end