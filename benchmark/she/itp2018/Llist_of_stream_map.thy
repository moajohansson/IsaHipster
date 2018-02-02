theory Llist_of_stream_map
  imports Main "$HIPSTER_HOME/IsaHipster"
    Lmap
    Smap
    Stream_of_llist_of_stream
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
(*cohipster llist_of_stream lmap smap*)
(* ca 70 sec *)
  
(* Why is this stl z and not just z? *)
lemma lemma_ac [thy_expl]: "llist_of_stream (smap y (stl z)) = lmap y (llist_of_stream (stl z))"
  by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.case_eq_if Lmap.lemma_ab llist_of_stream.disc_iff llist_of_stream.simps(2) llist_of_stream.simps(3) lmap.disc_iff(2) lmap.sel(1) smap.simps(1) smap.simps(2))
    
lemma lemma_ad [thy_expl]: "llist_of_stream (SCons y (smap z x2)) =
LCons y (lmap z (llist_of_stream x2))"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (smt Llist.distinct(1) Llist.sel(1) Llist.sel(3) Lmap.lemma_aa Stream.sel(1) Stream.sel(2) llist_of_stream.code lnull_def smap.code)
    
lemma lemma_ae [thy_expl]: "llist_of_stream (smap y (SCons z x2)) =
lmap y (LCons z (llist_of_stream x2))"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (metis (no_types, lifting) Lmap.lemma_aa Stream.sel(1) Stream.sel(2) lemma_ac llist_of_stream.code smap.simps(1) smap.simps(2))
    
lemma lemma_af [thy_expl]: "llist_of_stream (smap y (smap z x2)) = lmap y (lmap z (llist_of_stream x2))"
  by (coinduction arbitrary: x2 y z rule: Llist.Llist.coinduct_strong)
    (metis (mono_tags, lifting) Lmap.lemma_aa lemma_ac lemma_ae llist_of_stream.code smap.code)
end