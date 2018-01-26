theory Lappend_literates
  imports Main "$HIPSTER_HOME/IsaHipster"
    Lappend
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
 
primcorec literates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literates f x = LCons x (literates f (f x))"

cohipster literates lappend
(* Discovered and proved in ca. 20 seconds,
   lemmas about lappend are also discovered but discarded before proving 
   since they are already imported from Lappend.thy *)
lemma lemma_af [thy_expl]: "lappend (literates z x2) y = literates z x2"
 by (coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    auto
end