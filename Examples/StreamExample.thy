theory StreamExample
imports Main "$HIPSTER_HOME/IsaHipster"
begin
(* Set Hipster tactic*)
setup Tactic_Data.set_coinduct_sledgehammer 

codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")

primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"

(* Call Hipster for coinductive theory exploration *)
(*cohipster smap*)
lemma lemma_a [thy_expl]: "SCons (y z) (smap y x2) = smap y (SCons z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.coinduct_strong)
    simp  
 
(*cohipster smap Fun.id*)
lemma lemma_aa [thy_expl]: "smap id y = y"
  by(coinduction arbitrary: y rule: Stream.coinduct_strong)
    simp

(*cohipster smap Fun.comp*)
lemma lemma_ab [thy_expl]: "smap (y \<circ> z) x2 = smap y (smap z x2)"
  by(coinduction arbitrary: x2 y z rule: Stream.coinduct_strong)
auto

primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"
  
(*cohipster smap siterate*)
lemma lemma_ac [thy_expl]: "smap y (siterate y z) = siterate y (y z)"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
    auto
    
lemma lemma_ad [thy_expl]: "smap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
  by(coinduction arbitrary: x2 y z rule: Stream.coinduct_strong)
    (simp add: lemma_ac)

end