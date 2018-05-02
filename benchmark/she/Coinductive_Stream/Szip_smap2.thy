theory Szip_smap2
  imports Main "$HIPSTER_HOME/IsaHipster"
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

fun apsnd2 :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a,'b) Pair2 \<Rightarrow> ('a,'c) Pair2" where
"apsnd2 f (Pair2 a b) = Pair2 a (f b)"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream szip smap apsnd2
   
Proving: apsnd2 x2 (Pair22 z x3) = Pair22 z (x2 x3) 
Undefined fact: "Szip_smap2.Pair2.coinduct_strong"*)

theorem szip_smap2: 
 "szip xs (smap g ys) = smap (apsnd2 g) (szip xs ys)"
by hipster_coinduct_sledgehammer
end   