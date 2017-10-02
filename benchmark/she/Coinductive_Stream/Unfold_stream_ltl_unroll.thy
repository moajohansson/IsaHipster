theory Unfold_stream_ltl_unroll
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "unfold_stream g1 g2 a = SCons (g1 a) (unfold_stream g1 g2 (g2 a))"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream unfold_stream*)
(* No interesting results*)
theorem unfold_stream_ltl_unroll:
   "unfold_stream shd stl (stl b) = unfold_stream (shd \<circ> stl) stl b"
   by hipster_coinduct_sledgehammer

end    