theory Srecurse_siterate
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Stream" "types/Twople"
    "~~/src/HOL/Library/BNF_Corec"
    Hinze_Streams
begin
setup Tactic_Data.set_sledgehammer_coinduct 
setup Misc_Data.set_noisy
  
lemma recurse_simps[simp]:
      "stl (srecurse f a) = monomap f (srecurse f a)"
  by - (subst srecurse.code,simp)+
(*cohipster srecurse siterate*)
lemma lemma_az [thy_expl]: "SCons (y z) (monomap y x2) = monomap y (SCons z x2)"
  by (metis Stream.sel(1) Stream.sel(2) monomap.friend.code)
    
lemma lemma_ba [thy_expl]: "shd (srecurse y z) = z"
  by (metis Stream.sel(1) srecurse.code)
    
lemma lemma_bb [thy_expl]: "stl (srecurse y z) = srecurse y (y z)"
  by(coinduction rule: Hinze_Streams.srecurse.coinduct)
    (simp add: lemma_ba srecurse.cong_base srecurse.cong_monomap)
    
lemma lemma_bc [thy_expl]: "monomap y (srecurse y z) = srecurse y (y z)"
  using lemma_bb
  by (force simp add: lemma_bb)
    
lemma lemma_bd [thy_expl]: "SCons z (srecurse y (y z)) = srecurse y z"
  by (metis lemma_bc srecurse.code)
    
lemma lemma_be [thy_expl]: "monomap z (SCons y (srecurse z x2)) = SCons (z y) (srecurse z (z x2))"
  by (metis lemma_az lemma_bc)

lemma lemma_bf [thy_expl]: "srecurse y z = siterate y z"
proof(coinduction arbitrary: y z rule: Stream.Stream.coinduct_strong)
  case Eq_Stream thus ?case
    using lemma_ba lemma_bb
    by (force simp add: lemma_ba lemma_bb)
qed

lemma lemma_bg [thy_expl]: "monomap y (siterate y z) = siterate y (y z)"
 using lemma_bc lemma_bf
 by (force simp add: lemma_bc lemma_bf)

lemma lemma_bh [thy_expl]: "monomap z (SCons y (siterate z x2)) = SCons (z y) (siterate z (z x2))"
 by (metis lemma_az lemma_bg)
end