theory Smap_laws
  imports Main "$HIPSTER_HOME/IsaHipster"
    "../itp2018/types/Stream"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"
(*cohipster smap*)
lemma lemma_a [thy_expl]: "SCons (y z) (smap y x2) = smap y (SCons z x2)"
  by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    simp
(*cohipster smap Fun.id*)  \<comment> "Explore smap and identity funtcion"

(*cohipster smap Fun.comp*) \<comment> "Explore smap and function composition"
text_raw {*\DefineSnippet{smaplaws}{*}  
  
lemma lemma_aa [thy_expl]: "smap id y = y"
 by (coinduction arbitrary: y rule: Stream.Stream.coinduct_strong)
    simp
    
lemma lemma_ab [thy_expl]: "smap (y \<circ> z) x2 = smap y (smap z x2)"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto    
text_raw {*}%EndSnippet*}  

end