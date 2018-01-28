theory Siterate
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"

end