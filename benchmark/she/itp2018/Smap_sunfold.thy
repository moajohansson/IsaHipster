theory Smap_sunfold
  imports Main "$HIPSTER_HOME/IsaHipster"
    Smap
    Sunfold
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
(*cohipster smap sunfold*)
(* ca 25 sec *)
lemma lemma_ae [thy_expl]: "smap y (sunfold z z x2) = sunfold y z (z x2)"
 by (coinduction arbitrary: x2 y z rule: Stream.Stream.coinduct_strong)
    auto
(*cohipster smap sunfold Fun.comp*)
(* ca 30 sec *)
(* Functor fusion *)
lemma lemma_af [thy_expl]: "sunfold (y \<circ> z) x2 x3 = smap y (sunfold z x2 x3)"
 by (coinduction arbitrary: x2 x3 y z rule: Stream.Stream.coinduct_strong)
    auto
end