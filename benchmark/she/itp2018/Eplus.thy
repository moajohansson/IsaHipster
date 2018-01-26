theory Eplus
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/ENat"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
setup Misc_Data.set_noisy

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

(*cohipster eplus*)
(* Discovers and proves the following in just under 2 minutes *)

(* identity *)
lemma lemma_a [thy_expl]: "eplus x EZ = x"
 by (coinduction arbitrary: x rule: ENat.ENat.coinduct_strong)
    simp

lemma lemma_aa [thy_expl]: "eplus EZ x = x"
 by (coinduction arbitrary: x rule: ENat.ENat.coinduct_strong)
    simp

lemma lemma_ab [thy_expl]: "eplus (ESuc x) y = eplus x (ESuc y)"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    (metis ENat.discI(2) ENat.sel eplus.code)

lemma lemma_ac [thy_expl]: "ESuc (eplus x y) = eplus x (ESuc y)"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    (metis ENat.distinct(1) ENat.sel eplus.code is_zero_def)

lemma lemma_ad [thy_expl]: "eplus x (ESuc EZ) = ESuc x"
 by (coinduction arbitrary: x rule: ENat.ENat.coinduct_strong)
    (metis lemma_a lemma_ac)

(* associativity *)    
lemma lemma_ae [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
 by (coinduction arbitrary: x y z rule: ENat.ENat.coinduct_strong)
    auto

lemma lemma_af [thy_expl]: "epred (eplus x (ESuc y)) = eplus x y"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    auto

lemma lemma_ag [thy_expl]: "eplus y (eplus x z) = eplus x (eplus y z)"
 by (coinduction arbitrary: x y z rule: ENat.ENat.coinduct_strong)
    (smt eplus.code eplus.disc_iff(1) eplus.sel lemma_af)

lemma lemma_ah [thy_expl]: "eplus y (ESuc (ESuc x)) = eplus x (ESuc (ESuc y))"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    (metis ENat.discI(2) eplus.disc_iff(2) lemma_ad lemma_af lemma_ag)

(* commutativity *)    
lemma lemma_ai [thy_expl]: "eplus y x = eplus x y"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    (metis lemma_a lemma_ag)

lemma lemma_aj [thy_expl]: "eplus y (ESuc x) = eplus x (ESuc y)"
 by (coinduction arbitrary: x y rule: ENat.ENat.coinduct_strong)
    (metis ENat.discI(2) eplus.disc_iff(2) lemma_a lemma_af lemma_ag)
end