theory Szip_sconst2
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

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "shd (siterate f x) = x"
| "stl (siterate f x) = siterate f (f x)"  
  
(*abbreviation "sconst \<equiv> siterate id"*)
primcorec sconst :: "'a \<Rightarrow> 'a Stream" where
  "sconst x = SCons x (sconst x)"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream szip smap*)
  (*exception XML_BODY [] raised (line 397 of "PIDE/xml.ML") when exploring szip, smap*)
(*tip-spec output in outputSzipSmap file*)
theorem szip_sconst2: 
"szip xs (sconst b) = smap (\<lambda>x. (Pair2 x b)) xs"
  apply(coinduction arbitrary: xs)
  apply(auto)
    done
(* Why can't we automate this proof?*)
(*   by hipster_coinduct_sledgehammer results in following error:      
Failed to apply initial proof method\<here>:
goal (1 subgoal):
 1. szip xs (sconst b) = smap (\<lambda>x. Pair2 x b) xs
constants:
  Pure.prop :: prop \<Rightarrow> prop
  Pair2 :: 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Pair2
  smap :: ('a \<Rightarrow> ('a, 'b) Pair2) \<Rightarrow> 'a Stream \<Rightarrow> ('a, 'b) Pair2 Stream
  id :: 'b \<Rightarrow> 'b
  siterate :: ('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b Stream
  szip :: 'a Stream \<Rightarrow> 'b Stream \<Rightarrow> ('a, 'b) Pair2 Stream
  op = :: ('a, 'b) Pair2 Stream \<Rightarrow> ('a, 'b) Pair2 Stream \<Rightarrow> bool
  Trueprop :: bool \<Rightarrow> prop
  op \<Longrightarrow> :: prop \<Rightarrow> prop \<Rightarrow> prop*)
end   