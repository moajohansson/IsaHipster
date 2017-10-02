theory Pls_ac
  imports Main  "~~/src/HOL/Library/BNF_Corec" "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec pls :: "nat Stream \<Rightarrow> nat Stream \<Rightarrow> nat Stream" where
  "pls s t = SCons (plus (shd s) (shd t)) (pls (stl s) (stl t))"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"
(*hipster_obs Stream Lst obsStream pls
fins nothing *)
lemma pls_ac: "pls s (pls t u) = pls t (pls s u)"
  by hipster_coinduct_sledgehammer
    
end    

