theory Stream_applicative
  imports Main "$HIPSTER_HOME/IsaHipster"
    "../itp2018/types/Stream"
    "../itp2018/Smap"
begin
setup Tactic_Data.set_coinduct_sledgehammer 

text_raw {*\DefineSnippet{streamapplicative}{*}  
(* Lifting *)
primcorec spure :: "'a \<Rightarrow> 'a Stream" where  
  "shd (spure x) = x"
| "stl (spure x) = spure x"
  
(* Sequential application *)
primcorec sapp :: " ('a \<Rightarrow> 'b) Stream \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "shd (sapp fs xs) = (shd fs) (shd xs)"
| "stl (sapp fs xs) = sapp (stl fs) (stl xs)"
text_raw {*}%EndSnippet*} 
(*cohipster smap spure sapp*)
(* Discovered in ca 40 seconds *)
text_raw {*\DefineSnippet{streamapplout}{*}  
lemma lemma_ac [thy_expl]: "sapp (spure z) x2 = smap z x2"
  by (coinduction arbitrary: x2 z rule: Stream.Stream.coinduct_strong)
  auto

text_raw {*}%EndSnippet*} 
  
lemma lemma_ad [thy_expl]: "smap y (spure z) = spure (y z)"
  by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto
    
lemma lemma_ae [thy_expl]: "smap z (SCons y (spure x2)) = SCons (z y) (spure (z x2))"
  by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_ad)
    
lemma lemma_af [thy_expl]: "sapp (SCons y (spure z)) (spure x2) = SCons (y x2) (spure (z x2))"
  by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (simp add: Stream_applicative.lemma_ac lemma_ad)
end