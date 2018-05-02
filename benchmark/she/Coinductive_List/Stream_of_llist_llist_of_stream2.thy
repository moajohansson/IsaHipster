theory Stream_of_llist_llist_of_stream2
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
  
datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"
hipster_obs Stream Lst obsStream stream_of_llist2 llist_of_stream2
(* Nothing found *) 
(* Would need an observer for the llist also but can only 
have one at a time now*)

theorem stream_of_llist_llist_of_stream2:
  "stream_of_llist2 (llist_of_stream2 xs) = xs"
  by hipster_coinduct_sledgehammer
end