theory Llength_lappend
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
    "types/ENat"
    "Llength"
    "Lappend"
    "Eplus"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy
(*cohipster llength lappend eplus*)
(*Finds and proves the following in ca. 75 seconds*)
lemma lemma_ak [thy_expl]: "eplus (llength y) (llength z) = llength (lappend y z)"
 by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
    auto

lemma lemma_al [thy_expl]: "llength (ltl (lappend z y)) = llength (ltl (lappend y z))"
 by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
    (smt Llist.case_eq_if lemma_ai lemma_ak llength.disc(1) llength.disc(2) llength.sel ltl_def)

lemma lemma_am [thy_expl]: "llength (lappend z (LCons y x2)) = ESuc (llength (lappend z x2))"
 by (coinduction arbitrary: x2 y z rule: ENat.ENat.coinduct_strong)
    (metis ENat.distinct(1) ENat.sel Llength.lemma_a is_zero_def lappend.disc_iff(1) lemma_af lemma_ak llength.disc_iff(1))

lemma lemma_an [thy_expl]: "eplus (ESuc (llength y)) (llength z) = ESuc (llength (lappend y z))"
  by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
     (auto simp add: lemma_ak)

lemma lemma_ao [thy_expl]: "llength (lappend z y) = llength (lappend y z)"
 by (coinduction arbitrary: y z rule: ENat.ENat.coinduct_strong)
    (metis lappend.disc_iff(1) lemma_al llength.disc_iff(1) llength.sel)
end