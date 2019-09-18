theory Smap_siterate_comp
  imports Main "$HIPSTER_HOME/IsaHipster"
    Smap_laws
begin
setup Tactic_Data.set_coinduct_sledgehammer
primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"
(*cohipster smap siterate*)
lemma lemma_ac [thy_expl]: "smap y (siterate y z) = siterate y (y z)"
  by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto

lemma lemma_ad [thy_expl]: "smap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_ac)
(*cohipster smap siterate Fun.comp \<comment> "Explore smap, siterate, and function composition"
*)
text_raw \<open>\DefineSnippet{siteratefusion}{\<close>
lemma lemma_ae [thy_expl]: "smap z (siterate (y \<circ> z) x2) = siterate (z \<circ> y) (z x2)"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto
text_raw \<open>}%EndSnippet\<close>
      

end