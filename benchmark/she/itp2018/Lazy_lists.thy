theory Lazy_lists
  imports Main
    Smap Siterate
begin
  codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

primcorec lmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Llist \<Rightarrow> 'b Llist" where
 "lmap f xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap f xs))"  

primcorec literate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Llist" 
where "literate f x = LCons x (literate f (f x))"

codatatype ENat = is_zero: EZ | ESuc (epred: ENat)

primcorec eplus :: "ENat \<Rightarrow> ENat \<Rightarrow> ENat" where
"eplus m n = (if is_zero m then n else ESuc (eplus (epred m) n))"

primcorec llength :: "'a Llist \<Rightarrow> ENat" where
"llength xs = (if lnull xs then EZ else ESuc (llength (ltl xs)))" 

primcorec ltake :: "ENat \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist"
where
  "is_zero n \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

fun to_llist :: "'a list \<Rightarrow> 'a Llist" where
  "to_llist [] = LNil"
| "to_llist (Cons x xs) = LCons x (to_llist xs)"

primcorec llist_of_stream :: "'a Stream \<Rightarrow> 'a Llist"
  where "llist_of_stream s = LCons (shd s) (llist_of_stream (stl s))"

(*cohipster lappend *)
(*ca 25 seconds*)
(* lappend_LNil2 *)
lemma lemma_ac [thy_expl]: "lappend y LNil = y"
  by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    simp

lemma lemma_ad [thy_expl]: "lappend LNil y = y"
 by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    simp

lemma lemma_ae [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
 by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    (metis lappend.simps(4) lemma_ac lnull_def)

lemma lemma_af [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"

 by (simp add: lappend.code)
(* lappend_assoc *)
lemma lemma_ag [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    auto

lemma lemma_ah [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
 by(coinduction arbitrary: y rule: Llist.coinduct_strong)
    (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)
(*cohipster lmap *)
(* ca 5 seconds *)
lemma lemma_ai [thy_expl]: "lmap y (LCons z LNil) = LCons (y z) LNil"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    simp

lemma lemma_aj [thy_expl]: "LCons (y z) (lmap y x2) = lmap y (LCons z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    simp
(*cohipster lmap lappend *)
(*ca 80 seconds*)
lemma lemma_ak [thy_expl]: "ltl (lmap y z) = lmap y (ltl z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Llist.case_eq_if Llist.collapse(2) Llist.inject lemma_aj lmap.disc_iff(2) lnull_def ltl_def)

lemma lemma_al [thy_expl]: "ltl (lappend z (lmap y z)) = lappend (ltl z) (lmap y z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis lappend.simps(4) lemma_ac lmap.ctr(1))

lemma lemma_am [thy_expl]: "ltl (lappend (lmap y z) z) = lappend (lmap y (ltl z)) z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Llist.sel(2) lappend.disc_iff(1) lappend.simps(4) lemma_ak lmap.disc_iff(2) lnull_def)

lemma lemma_an [thy_expl]: "ltl (lappend (lmap y z) (ltl z)) = lappend (lmap y (ltl z)) (ltl z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Llist.sel(2) lappend.ctr(1) lappend.simps(4) lemma_ak lmap.ctr(1) lmap.disc_iff(2))

(*lmap_lappend_distrib*)
lemma lemma_ao [thy_expl]: "lappend (lmap y z) (lmap y x2) = lmap y (lappend z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt Llist.collapse(2) Llist.sel(1) lappend.disc_iff(1) lappend.simps(3) lappend.simps(4) lemma_aj lemma_ak lmap.disc_iff(2))
(*cohipster literate *)
(*Discovers nothing interesting - 3 seconds ish*)
(*cohipster llength *)
(* ca 4 seconds *)
(*llength_LCons*)
lemma lemma_ap [thy_expl]: "llength (LCons y z) = ESuc (llength z)"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    simp
(*cohipster lappend literate*)
(* 23 seconds *)
(* lappend_iterates *)
lemma lemma_aq [thy_expl]: "lappend (literate z x2) y = literate z x2"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    auto
(*cohipster llength lappend *)
(* 65 seconds *)
lemma lemma_ar [thy_expl]: "llength (lappend z (LCons y x2)) = ESuc (llength (lappend z x2))"
 by(coinduction arbitrary: x2 y z rule: ENat.coinduct_strong)
    (smt ENat.distinct(1) ENat.sel Llist.discI(2) Llist.sel(3) is_zero_def lappend.disc_iff(1) lappend.simps(4) llength.ctr(1) llength.ctr(2))

lemma lemma_as [thy_expl]: "llength (lappend z y) = llength (lappend y z)"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    (metis ENat.sel Lazy_lists.lemma_ar Llist.collapse(2) lappend.disc_iff(1) lappend.simps(4) llength.disc_iff(2) llength.sel)

lemma lemma_at [thy_expl]: "llength (ltl (lappend z y)) = llength (ltl (lappend y z))"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    (metis lemma_as llength.disc_iff(2) llength.sel lnull_def)
(*cohipster eplus *)
(* 85 seconds *)
lemma lemma_au [thy_expl]: "eplus x EZ = x"
 by(coinduction arbitrary: x rule: ENat.coinduct_strong)
    simp
(*178*)
lemma lemma_av [thy_expl]: "eplus EZ x = x"
 by(coinduction arbitrary: x rule: ENat.coinduct_strong)
    simp
(*iadd_Suc_right*)
lemma lemma_aw [thy_expl]: "ESuc (eplus x y) = eplus x (ESuc y)"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    (metis ENat.distinct(1) ENat.sel eplus.code is_zero_def)
(*  eSuc_plus_1 *)
lemma lemma_ax [thy_expl]: "eplus x (ESuc EZ) = ESuc x"
 by(coinduction arbitrary: x rule: ENat.coinduct_strong)
    (metis lemma_au lemma_aw)

lemma lemma_ay [thy_expl]: "eplus y (ESuc x) = eplus x (ESuc y)"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    (metis ENat.collapse(2) ENat.disc(2) eplus.sel lemma_au lemma_aw)
(*174*)
lemma lemma_az [thy_expl]: "eplus (eplus x y) z = eplus x (eplus y z)"
 by(coinduction arbitrary: x y z rule: ENat.coinduct_strong)
    auto

lemma lemma_ba [thy_expl]: "eplus y (ESuc (ESuc x)) = eplus x (ESuc (ESuc y))"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    (metis lemma_aw lemma_ay)

lemma lemma_bb [thy_expl]: "epred (eplus x (ESuc y)) = eplus x y"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    auto
(*176*)
lemma lemma_bc [thy_expl]: "eplus y x = eplus x y"
 by(coinduction arbitrary: x y rule: ENat.coinduct_strong)
    (metis lemma_ay lemma_bb)

lemma lemma_bd [thy_expl]: "eplus y (eplus x z) = eplus x (eplus y z)"
proof(coinduction arbitrary: x y z rule: ENat.coinduct_strong)
  case Eq_ENat thus ?case
    using lemma_az lemma_bc
    by (force simp add: lemma_az lemma_bc)
qed
  
(*cohipster llength lappend eplus *)
(* 30 seconds *)
(*llength_lappend*)
lemma lemma_be [thy_expl]: "eplus (llength y) (llength z) = llength (lappend y z)"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    auto

lemma lemma_bf [thy_expl]: "eplus (ESuc (llength y)) (llength z) = ESuc (llength (lappend y z))"
proof(coinduction arbitrary: y z rule: ENat.coinduct_strong)
  case Eq_ENat thus ?case
    using lemma_be
    by (force simp add: lemma_be)
qed

(*cohipster llength lmap*)
(* 18 seconds *)
(* llength_lmap *)
lemma lemma_bg [thy_expl]: "llength (lmap y z) = llength z"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    (metis lemma_ak llength.disc_iff(2) llength.sel lmap.disc_iff(2))

(*cohipster ltake *)
(* ca 80 seconds *)
lemma lemma_bh [thy_expl]: "ltake y (ltake y z) = ltake y z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    auto
(*ltake_ltl*)
lemma lemma_bi [thy_expl]: "ltl (ltake (ESuc y) z) = ltake y (ltl z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis ENat.disc(2) ENat.sel Llist.sel(2) lnull_def ltake.disc(1) ltake.simps(4))

lemma lemma_bj [thy_expl]: "ltake z (ltake y x2) = ltake y (ltake z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    auto

lemma lemma_bk [thy_expl]: "ltake y (ltake (ESuc y) z) = ltake y z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt ENat.collapse(2) ENat.disc(2) lemma_bi ltake.disc_iff(2) ltake.simps(3))

lemma lemma_bl [thy_expl]: "ltake y (ltl (ltake y z)) = ltl (ltake y z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Llist.sel(2) ltake.ctr(1) ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))
(*ltake_eSuc_LCons*)
lemma lemma_bm [thy_expl]: "ltake (ESuc z) (LCons y x2) = LCons y (ltake z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    simp

lemma lemma_bn [thy_expl]: "ltake y (LCons z (ltake y x2)) = ltake y (LCons z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt Llist.disc(2) Llist.sel(1) Llist.sel(3) lemma_bj lemma_bl ltake.disc_iff(2) ltake.simps(3) ltake.simps(4))

lemma lemma_bo [thy_expl]: "ltake (ESuc y) (ltl (ltake y z)) = ltl (ltake y z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis lemma_bi lemma_bl)

lemma lemma_bp [thy_expl]: "ltake (ESuc (ESuc y)) (ltake y z) = ltake y z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis ENat.disc(2) lemma_bi lemma_bo ltake.disc_iff(2) ltake.simps(3))

lemma lemma_bq [thy_expl]: "ltake (ESuc EZ) (ltake (ESuc y) z) = ltake (ESuc EZ) z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (simp add: ltake.ctr(1))
(*cohipster ltake lmap*)
(* 32 seconds *)
(* ltake_lmap *)
lemma lemma_br [thy_expl]: "ltake z (lmap y x2) = lmap y (ltake z x2)"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt ENat.collapse(2) Llist.case_eq_if Llist.sel(1) lemma_ak lemma_bi lmap.disc_iff(2) lmap.sel(1) ltake.ctr(2) ltake.disc_iff(2))

(*cohipster llist_of_stream *)
(* 5 seconds *)
lemma lemma_bw [thy_expl]: "llist_of_stream (SCons y z) = LCons y (llist_of_stream z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    simp
(*cohipster llist_of_stream smap lmap *)
(* 41 seconds *)
lemma lemma_bx [thy_expl]: "llist_of_stream (smap y z) = lmap y (llist_of_stream z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (smt Llist.case_eq_if lemma_ak llist_of_stream.disc_iff llist_of_stream.simps(2) llist_of_stream.simps(3) lmap.disc_iff(2) lmap.sel(1) smap.simps(1) smap.simps(2))
(*cohipster llist_of_stream literate siterate *)
(* 23 seconds *)
lemma lemma_by [thy_expl]: "llist_of_stream (siterate y z) = literate y z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    auto
(*cohipster lmap literate *)
(* 45 seconds *)
lemma lemma_bz [thy_expl]: "lmap z (LCons y (literate z x2)) = LCons (z y) (literate z (z x2))"
 by(coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    (smt Llist.distinct(1) Llist.sel(1) Llist.sel(3) lemma_aj literate.code lnull_def)
(* lmap_iterates *)
lemma lemma_ca [thy_expl]: "lmap y (literate y z) = literate y (y z)"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis lemma_bz literate.code)

(*cohipster to_llist lappend append *)
(* 80 seconds *)
(* lappend_llist_of_llist_of *)
lemma lemma_cb [thy_expl]: "lappend (to_llist y) (to_llist z) = to_llist (y @ z)"
apply (induct y arbitrary: z)
apply (simp add: lemma_ad)
apply (simp add: lappend.code)
  done
(*cohipster to_llist lmap map *)
(* 65 seconds *)
(*lmap_llist_of*)
lemma lemma_cc [thy_expl]: "to_llist (map y z) = lmap y (to_llist z)"
apply (induct z)
apply (simp add: lmap.ctr(1))
apply (simp add: lemma_aj)
  done
end