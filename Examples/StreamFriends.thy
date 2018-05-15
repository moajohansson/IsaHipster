theory StreamFriends
  imports Main "$HIPSTER_HOME/IsaHipster"
    "~~/src/HOL/Library/BNF_Corec"
begin
(* Set Hipster tactic *)
setup Tactic_Data.set_sledgehammer_coinduct 
  
codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")
primcorec siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "siterate f a = SCons a (siterate f (f a))"
primcorec monomap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Stream \<Rightarrow> 'a Stream" where
  "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"
friend_of_corec monomap where
   "monomap f xs = SCons (f (shd xs)) (monomap f (stl xs))"
  by (auto intro: monomap.code)

corec srecurse :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Stream" where
  "srecurse f a = SCons a (monomap f (srecurse f a))"
(*
lemma recurse_simps[simp]:
      "stl (srecurse f a) = monomap f (srecurse f a)"
  by - (subst srecurse.code,simp)+
*)
(* Call Hipster for coinductive theory exploration *)
cohipster srecurse siterate
lemma lemma_a [thy_expl]: "monomap y (siterate y z) = siterate y (y z)"
  by(coinduction arbitrary: y z rule: Stream.coinduct_strong)
    auto

lemma lemma_aa [thy_expl]: "monomap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
  by (metis Stream.sel(1) Stream.sel(2) StreamFriends.lemma_a monomap.friend.code)

lemma lemma_ab [thy_expl]: "srecurse y z = siterate y z"
  by(coinduction rule: srecurse.coinduct)
    (smt Stream.sel(1) Stream.sel(2) lemma_a siterate.code srecurse.code srecurse.cong_base srecurse.cong_monomap)


end