theory Lazy_List
  imports Main "$HIPSTER_HOME/IsaHipster"
begin
setup Tactic_Data.set_coinduct_sledgehammer 
(*setup Tactic_Data.set_no_proof*) (* For measuring exploration time *)
setup Misc_Data.set_time (* Print out timing info *)
setup Misc_Data.set_noisy (* Verbose output on hipster calls *)

(* Lazy list codatatype *)
codatatype (lset: 'a) Llist =
      lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

(* Appending lazy lists *)
primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "lappend xs ys = (case xs of LNil \<Rightarrow> ys | LCons x xs' \<Rightarrow> LCons x (lappend xs' ys))"

cohipster lappend
(* The lemmas and proofs below are the output of the hipster call above 
   lemma_ac is lappend_LNil2 and lemma_ab is lappend_assoc from Coinductive_List *)
lemma lemma_a [thy_expl]: "lappend LNil y = y"
  by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    (simp add: lappend.code)

lemma lemma_aa [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    simp

lemma lemma_ab [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt Llist.collapse(1) Llist.collapse(2) Llist.simps(4) Llist.simps(5) lappend.code lappend.disc(1) lappend.disc_iff(1) lappend.simps(4) lhd_def)

lemma lemma_ac [thy_expl]: "lappend y LNil = y"
  by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    (smt Llist.collapse(2) Llist.disc_eq_case(1) Llist.simps(4) Llist.simps(5) lappend.code lappend.simps(4) lhd_def lnull_def)

(* Mapping a function over a lazy list *)
primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"

cohipster lmap
(* The lemmas and proofs below are the output of the hipster call above *)

lemma lemma_ad [thy_expl]: "lmap z (LCons x2 LNil) = LCons (z x2) LNil"
  by(coinduction arbitrary: x2 z rule: Llist.coinduct_strong)
simp

lemma lemma_ae [thy_expl]: "LCons (z x2) (lmap z x3) = lmap z (LCons x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Llist.coinduct_strong)
    simp

lemma lemma_af [thy_expl]: "LCons (z x2) (LCons (z x3) LNil) = lmap z (LCons x2 (LCons x3 LNil))"
by(coinduction arbitrary: x2 x3 z rule: Llist.coinduct_strong)
  (simp add: lemma_ad)

cohipster lmap lappend
(* The lemmas and proofs below are the output of the hipster call above
   lemma_ag is lmap_lappend_distrib from Coinductive_List *)
lemma lemma_ag [thy_expl]: "lappend (lmap z x2) (lmap z x3) = lmap z (lappend x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Llist.coinduct_strong)
    (smt Llist.case_eq_if lappend.disc_iff(1) lappend.simps(3) lappend.simps(4) lmap.disc_iff(2) lmap.simps(3) lmap.simps(4))

(* Converting a standard list to a lazy list *)
primrec llist_of :: "'a list \<Rightarrow> 'a Llist"
where
  "llist_of [] = LNil"
| "llist_of (x#xs) = LCons x (llist_of xs)"


cohipster llist_of lappend append
(* The lemmas and proofs below are the output of the hipster call above
   lemma_ah is lappend_llist_of_llist_of from Coinductive_List *)
lemma lemma_ah [thy_expl]: "lappend (llist_of y) (llist_of z) = llist_of (y @ z)"
  apply (induct y arbitrary: z)
  apply (simp add: lappend.code)
  apply (simp add: lemma_aa)
  done

cohipster llist_of lmap map
(* The lemmas and proofs below are the output of the hipster call above
   lemma_ai is lmap_llist_of from Coinductive_List *)
lemma lemma_ai [thy_expl]: "lmap z (llist_of x2) = llist_of (map z x2)"
  apply (induct x2)
  apply simp
  apply (metis lemma_ae list.simps(9) llist_of.simps(2))
  done

(* Extended natural numbers *)
codatatype ENat = is_zero: EZ | ESuc (epred: ENat)

(* Length of a lazy list *)
primcorec llength :: "'a Llist \<Rightarrow> ENat" where
"llength xs = (case xs of LNil \<Rightarrow> EZ | LCons y ys \<Rightarrow> ESuc (llength ys))"

cohipster llength
(* The lemmas and proofs below are the output of the hipster call above *)
lemma lemma_aj [thy_expl]: "llength (LCons y z) = ESuc (llength z)"
  by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    simp

cohipster llength lmap
(* The lemmas and proofs below are the output of the hipster call above
   lemma_ak is llength_lmap from Coinductive_List *)
lemma lemma_ak [thy_expl]: "llength (lmap z x2) = llength x2"
  by(coinduction arbitrary: x2 z rule: ENat.coinduct_strong)
    (metis Llist.case_eq_if llength.disc_iff(2) llength.sel lmap.disc_iff(2) lmap.simps(4))

(* Addition on extended natural numbers *)
primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

cohipster eplus
(* The lemmas and proofs below are the output of the hipster call above
   lemma_am is iadd_Suc_right and lemma_an and unknown lemma in line 130
   are proved in lines 171-180 of Extended_Nat *)
lemma lemma_al [thy_expl]: "eplus x EZ = x"
  by(coinduction arbitrary: x rule: ENat.coinduct_strong)
simp

lemma lemma_am [thy_expl]: "eplus x (ESuc y) = ESuc (eplus x y)"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    (metis ENat.disc(2) ENat.sel eplus.code)

lemma lemma_an [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
  by(coinduction arbitrary: x y z rule: ENat.coinduct_strong)
auto

lemma unknown [thy_expl]: "eplus y x = eplus x y"
  oops

cohipster llength lappend eplus
(* The lemmas and proofs below are the output of the hipster call above
   lemma_aq is llength_lappend from Coinductive_List *)
lemma lemma_ao [thy_expl]: "eplus EZ (llength y) = llength y"
  by(coinduction arbitrary: y rule: ENat.coinduct_strong)
    simp

lemma lemma_ap [thy_expl]: "eplus (ESuc y) (llength z) = ESuc (eplus y (llength z))"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
simp

lemma lemma_aq [thy_expl]: "eplus (llength y) (llength z) = llength (lappend y z)"
  by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
(smt ENat.sel Llist.case_eq_if eplus.disc_iff(1) eplus.sel lappend.ctr(2) lappend.disc_iff(1) lemma_aj llength.disc_iff(2) llength.sel)

lemma lemma_ar [thy_expl]: "llength (lappend z (LCons y x2)) = ESuc (llength (lappend z x2))"
by(coinduction arbitrary: x2 y z rule: ENat.coinduct_strong)
  (metis Lazy_List.lemma_aq lemma_aj lemma_am)

lemma lemma_as [thy_expl]: "llength (lappend z y) = llength (lappend y z)"
by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
  (smt ENat.sel Lazy_List.lemma_aq Llist.case_eq_if eplus.code lappend.disc_iff(1) lemma_am llength.ctr(2) llength.disc_iff(2))

lemma unknown [thy_expl]: "eplus y x = eplus x y"
  oops

(* Taking from a lazy list *)
primcorec ltake :: "ENat \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"ltake n xs = (case xs of LNil \<Rightarrow> LNil 
                  | LCons y ys \<Rightarrow> (case n of EZ \<Rightarrow> LNil | ESuc n \<Rightarrow> LCons y (ltake n ys)
                                  )
               )"

cohipster ltake
(* The lemmas and proofs below are the output of the hipster call above *)
lemma lemma_at [thy_expl]: "ltake z (ltake y x2) = ltake y (ltake z x2)"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
(smt ENat.case_eq_if Llist.case_eq_if ltake.disc(1) ltake.disc(2) ltake.simps(3) ltake.simps(4))

lemma lemma_au [thy_expl]: "ltake y (ltake y z) = ltake y z"
by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  (smt ENat.collapse(2) ENat.simps(5) Llist.collapse(2) Llist.simps(5) ltake.disc_iff(1) ltake.simps(3) ltake.simps(4))

lemma lemma_av [thy_expl]: "ltake y (ltake (ESuc y) z) = ltake y z"
by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  (smt ENat.collapse(2) ENat.discI(2) ENat.simps(5) Llist.case_eq_if ltake.disc(1) ltake.disc(2) ltake.simps(3) ltake.simps(4))

lemma lemma_aw [thy_expl]: "ltake (ESuc z) (LCons y x2) = LCons y (ltake z x2)"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    simp

lemma lemma_ax [thy_expl]: "ltake y (LCons z (ltake y x2)) = ltake y (LCons z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (metis Lazy_List.lemma_aw lemma_av)

lemma lemma_ay [thy_expl]: "ltake y (ltake (ESuc (ESuc y)) z) = ltake y z"
by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  (metis lemma_av)

lemma lemma_az [thy_expl]: "ltake (ESuc y) (ltake (ESuc EZ) z) = ltake (ESuc EZ) z"
by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  (smt ENat.disc(1) Lazy_List.lemma_aw Llist.collapse(2) Llist.disc(1) ltake.ctr(1))

cohipster ltake lmap
(* The lemmas and proofs below are the output of the hipster call above
   lemma_ba is ltake_lmap from Coinductive_List *)
lemma lemma_ba [thy_expl]: "ltake x2 (lmap z x3) = lmap z (ltake x2 x3)"
  by(coinduction arbitrary: x2 x3 z rule: Llist.coinduct_strong)
    (smt ENat.collapse(2) Llist.collapse(2) Llist.sel(1) Llist.sel(3) lemma_ae lemma_aw lmap.disc_iff(2) ltake.disc(1) ltake.disc(2))

lemma lemma_bb [thy_expl]: "lmap x2 (ltake z (LCons x3 LNil)) = ltake z (LCons (x2 x3) LNil)"
  by(coinduction arbitrary: x2 x3 z rule: Llist.coinduct_strong)
    (metis lemma_ad lemma_ba)

(* Iteratively building a lazy list from a function and an element *)
primcorec iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "iterates f x = LCons x (iterates f (f x))"

cohipster lmap iterates
(* The lemmas and proofs below are the output of the hipster call above
   lemma_bc is ltake_lmap from Coinductive_List *)
lemma lemma_bc [thy_expl]: "lmap y (iterates y z) = iterates y (y z)"
  by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Lazy_List.iterates.simps(2) Llist.case_eq_if Llist.sel(3) iterates.code lemma_ae lmap.disc_iff(2) lmap.simps(3) lnull_def)

lemma lemma_bd [thy_expl]: "lmap z (LCons y (iterates z x2)) = LCons (z y) (iterates z (z x2))"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (simp add: lemma_bc)

cohipster lappend iterates
(* The lemmas and proofs below are the output of the hipster call above
   lemma_be is lmap_iterates from Coinductive_List *)
lemma lemma_be [thy_expl]: "lappend (iterates z x2) y = iterates z x2"
  by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt Llist.sel(3) Llist.simps(5) iterates.code iterates.disc_iff lappend.disc_iff(2) lemma_aa lhd_def)

end

