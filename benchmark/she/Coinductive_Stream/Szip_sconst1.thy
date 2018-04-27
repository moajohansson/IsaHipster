theory Szip_sconst1
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

(*hipster_obs Stream Lst obsStream szip sconst smap
lemma lemma_a [thy_expl]: "smap y (sconst z) = sconst (y z)"
  apply (coinduction  arbitrary: y z rule: Szip_sconst1.Stream.coinduct_strong)
  apply simp
  by auto
    
lemma lemma_aa [thy_expl]: "smap z (SCons y (sconst x2)) = SCons (z y) (sconst (z x2))"
apply (coinduction  arbitrary: x2 y z rule: Szip_sconst1.Stream.coinduct_strong)
by (simp_all add: lemma_a)

lemma unknown [thy_expl]: "szip (sconst y) (sconst z) = sconst (Pair22 y z)"
oops*)
(* with old def of sconst exception TYPE raised (line 117 of "consts.ML"): Not a logical constant: "Szip_sconst1.sconst"*)
theorem szip_sconst1: 
 "szip (sconst a) xs = smap (\<lambda>x. (Pair2 a x)) xs"
  by hipster_coinduct_sledgehammer
end   