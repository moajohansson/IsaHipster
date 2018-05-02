theory Lzip_llist_of_stream2
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
datatype ('a, 'b) Pair2 = Pair2 'a 'b 
primcorec lzip :: "'a Llist \<Rightarrow> 'b Llist \<Rightarrow> (('a, 'b) Pair2) Llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (Pair2 (lhd xs) (lhd ys))"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"  

primcorec szip :: "'a Stream \<Rightarrow> 'b Stream \<Rightarrow> (('a, 'b) Pair2) Stream" where
  "shd (szip s1 s2) = Pair2 (shd s1) (shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"
  
theorem lzip_llist_of_stream2:
  "lzip (llist_of_stream2 xs) (llist_of_stream2 ys) = llist_of_stream2 (szip xs ys)"
  by hipster_coinduct_sledgehammer

end