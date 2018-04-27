theory Smap_unfold_stream
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "unfold_stream g1 g2 a = SCons (g1 a) (unfold_stream g1 g2 (g2 a))"


datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"
fun shead :: "'a Stream \<Rightarrow> 'a" where
  "shead xs = shd xs"
fun stail :: "'a Stream \<Rightarrow> 'a Stream" where
  "stail xs = stl xs"
(*hipster_obs Stream Lst obsStream smap unfold_stream shead stail
*)
lemma lemma_a [thy_expl]: "smap y (unfold_stream z z x2) = unfold_stream y z (z x2)"
  apply (coinduction  arbitrary: x2 y z rule: Smap_unfold_stream.Stream.coinduct_strong)
  apply simp
  by auto
theorem smap_unfold_stream:
  "smap f (unfold_stream shead stail b) = unfold_stream (f \<circ> shead) stail b"
by hipster_coinduct_sledgehammer

end    