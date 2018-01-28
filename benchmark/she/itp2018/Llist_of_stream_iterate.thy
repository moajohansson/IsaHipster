theory Llist_of_stream_iterate
  imports Main "$HIPSTER_HOME/IsaHipster"
    Literate
    Siterate
    Stream_of_llist_of_stream
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
(*cohipster llist_of_stream siterate literate*)
(*ca 20 sec*)
lemma lemma_ac [thy_expl]: "llist_of_stream (siterate y z) = literate y z"
 by (coinduction arbitrary: y z rule: Llist.Llist.coinduct_strong)
    auto
end