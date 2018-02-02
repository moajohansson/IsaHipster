theory Sunfold_laws
  imports Main "$HIPSTER_HOME/IsaHipster"
    "../itp2018/types/Stream"
    Smap_laws
begin
setup Tactic_Data.set_coinduct_sledgehammer 
text_raw {*\DefineSnippet{sunfolddef}{*}
primcorec sunfold :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "sunfold g f a = SCons (g a) (sunfold g f (f a))"
text_raw {*}%EndSnippet*}  
(*cohipster sunfold Fun.comp \<comment> "Explore sunfold and function composition"*)  
text_raw {*\DefineSnippet{sunfoldfusion}{*}
lemma lemma_ac [thy_expl]: "sunfold (z \<circ> x2) x2 x3 = sunfold z x2 (x2 x3)"
  by (coinduction arbitrary: x2 x3 z rule: Stream.Stream.coinduct_strong)
    auto
text_raw {*}%EndSnippet*} 
(*cohipster sunfold smap Fun.comp*) \<comment> "Explore sunfold, smap, and function composition"

lemma lemma_ad [thy_expl]: "smap y (sunfold z z x2) = sunfold y z (z x2)"
  by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
  auto
text_raw {*\DefineSnippet{sunfoldfunctorfusion}{*}
  
lemma lemma_ae [thy_expl]: "sunfold (y \<circ> z) x2 x3 = smap y (sunfold z x2 x3)"
 by (coinduction arbitrary: x2 x3 y z rule: Stream.Stream.coinduct_strong)
    auto
text_raw {*}%EndSnippet*}
  
end