theory Smap_fst_szip
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")
datatype ('a, 'b) Pair2 = Pair2 'a 'b
primcorec szip :: "'a Stream \<Rightarrow> 'b Stream \<Rightarrow> (('a, 'b) Pair2) Stream" where
  "shd (szip s1 s2) = Pair2 (shd s1) (shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"

fun fst2 :: "('a,'b) Pair2 \<Rightarrow> 'a" where
"fst2 (Pair2 a b) = a"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream szip smap fst2
Proving: fst2 (Pair22 x2 z) = x2 
Undefined fact: "Smap_fst_szip.Pair2.coinduct_strong"*)
theorem smap_fst_szip: 
  "smap fst2 (szip xs ys) = xs"
by hipster_coinduct_sledgehammer
end   