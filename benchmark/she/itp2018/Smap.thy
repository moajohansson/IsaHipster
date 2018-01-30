theory Smap
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream"
    
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
primcorec smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Stream \<Rightarrow> 'b Stream" where
  "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"
(* cohipster smap *)
(* Discovered in ca. 15 sec *)
lemma lemma_a [thy_expl]: "SCons (y z) (smap y x2) = smap y (SCons z x2)"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    simp
(*cohipster smap Fun.id*)
(* Discovered in ca. 15 sec *)
lemma lemma_aa [thy_expl]: "smap id y = y"
  by (coinduction arbitrary: y rule: Stream.Stream.coinduct_strong)
    simp
(*cohipster smap Fun.comp*)
(* Discovered in ca. 30 seconds *)
lemma lemma_ab [thy_expl]: "smap (y \<circ> z) x2 = smap y (smap z x2)"
  by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto

end