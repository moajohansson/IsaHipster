theory Szip
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream"
    "types/Twople"
    Smap
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
primcorec szip :: "'a Stream \<Rightarrow> 'b Stream \<Rightarrow> (('a, 'b) Twople) Stream" where
  "shd (szip s1 s2) = Pair2 (shd s1) (shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"

(*cohipster szip smap fst2 Fun.id*)

end