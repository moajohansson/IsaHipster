theory Unfold_stream
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b Stream" where
  "unfold_stream g1 g2 a = SCons (g1 a) (unfold_stream g1 g2 (g2 a))"

(* cohipster unfold_stream Fun.comp *)
(* Discovered and proved in ca 80 seconds *)
lemma lemma_a [thy_expl]: "unfold_stream (z \<circ> x2) x2 x3 = unfold_stream z x2 (x2 x3)"
  by (coinduction arbitrary: x2 x3 z rule: Stream.Stream.coinduct_strong)
    auto

end