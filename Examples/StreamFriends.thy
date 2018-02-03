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

lemma recurse_simps[simp]:
      "stl (srecurse f a) = monomap f (srecurse f a)"
  by - (subst srecurse.code,simp)+

(* Call Hipster for coinductive theory exploration *)
(*cohipster srecurse siterate*)
lemma lemma_a [thy_expl]: "SCons (y (shd z)) (monomap y x2) = monomap y (SCons (shd z) x2)"
 by (metis Stream.sel(1) Stream.sel(2) monomap.friend.code)

lemma lemma_aa [thy_expl]: "shd (srecurse y z) = z"
 by (metis Stream.sel(1) srecurse.code)

lemma lemma_ab [thy_expl]: "stl (srecurse y z) = srecurse y (y z)"
 by(coinduction rule: srecurse.coinduct)
    (simp add: lemma_aa srecurse.cong_base srecurse.cong_monomap)

lemma lemma_ac [thy_expl]: "monomap y (srecurse y z) = srecurse y (y z)"
 using lemma_ab
 by (force simp add: lemma_ab)

lemma lemma_ad [thy_expl]: "SCons z (srecurse y (y z)) = srecurse y z"
 by (metis lemma_ab recurse_simps srecurse.code)

lemma lemma_ae [thy_expl]: "SCons (y z) (monomap y x2) = monomap y (SCons z x2)"
 by (metis Stream.sel(1) Stream.sel(2) monomap.friend.code)

lemma lemma_af [thy_expl]: "monomap z (SCons y (srecurse z x2)) = SCons (z y) (srecurse z (z x2))"
 by (metis lemma_ac lemma_ae)

lemma lemma_ag [thy_expl]: "srecurse y z = siterate y z"
proof(coinduction arbitrary: y z rule: Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using lemma_aa lemma_ab
    by (force simp add: lemma_aa lemma_ab)
qed

lemma lemma_ah [thy_expl]: "monomap y (siterate y z) = siterate y (y z)"
 using lemma_ac lemma_ag
 by (force simp add: lemma_ac lemma_ag)

lemma lemma_ai [thy_expl]: "monomap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
 by (metis lemma_ae lemma_ah)
end