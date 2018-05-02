theory Prd_assoc
  imports Main  "~~/src/HOL/Library/BNF_Corec" "$HIPSTER_HOME/IsaHipster"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec pls :: "nat Stream \<Rightarrow> nat Stream \<Rightarrow> nat Stream" where
  "pls s t = SCons (plus (shd s) (shd t)) (pls (stl s) (stl t))"

friend_of_corec pls where
  "pls s t = SCons (plus (shd s) (shd t)) (pls (stl s) (stl t))"
   apply (rule pls.code)
  by transfer_prover

corec (friend) prd :: "nat Stream \<Rightarrow> nat Stream \<Rightarrow> nat Stream" where
  "prd s t = SCons ((shd s) * (shd t)) (pls (prd (stl s) t) (prd s (stl t)))"

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"
    
fun obsStream :: "int \<Rightarrow> 'a Stream \<Rightarrow> 'a Lst" where
"obsStream n s = (if (n \<le> 0) then Emp else Cons (shd s) (obsStream (n - 1) (stl s)))"

(*hipster_obs Stream Lst obsStream prd
Proving: times_nat x 0 = 0 
Undefined fact: "Nat.nat.coinduct_strong" *)

theorem prd_assoc: "prd s (prd t u) = prd (prd s t) u"
 (* by hipster_coinduct_sledgehammer
Failed to apply initial proof method *)
end  
