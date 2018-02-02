theory Smap_siterate
  imports Main "$HIPSTER_HOME/IsaHipster"
    Smap
    Siterate
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
(*cohipster smap siterate*)
(* ca 30 seconds *)
lemma lemma_ac [thy_expl]: "smap y (siterate y z) = siterate y (y z)"
 by (coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
    auto

lemma lemma_ad [thy_expl]: "smap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    (simp add: lemma_ac)
(*cohipster smap siterate Fun.comp*)
(*ca 1 minute*)
lemma lemma_ae [thy_expl]: "smap z (siterate (y \<circ> z) x2) = siterate (z \<circ> y) (z x2)"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto
end