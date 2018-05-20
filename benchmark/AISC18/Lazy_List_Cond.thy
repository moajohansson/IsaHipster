theory Lazy_List_Cond
  imports Main "$HIPSTER_HOME/IsaHipster"
          Lazy_List
begin
setup Tactic_Data.set_coinduct_sledgehammer_auto 
(*setup Tactic_Data.set_no_proof*) (* For measuring exploration time *)
setup Misc_Data.set_time (* Print out timing info *)
setup Misc_Data.set_noisy (* Verbose output on hipster calls *)


(* Discovering conditional lemmas *)

(* Exploration with lnull as a predicate *)
(*cohipster lnull lappend*)
lemma lemma_bf [thy_expl]: "lnull y = True \<Longrightarrow> lnull z = True \<Longrightarrow> y = z"
  by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
simp

lemma lemma_bg [thy_expl]: "lnull y = True \<Longrightarrow> LNil = y"
  by(coinduction arbitrary: y rule: Llist.coinduct_strong)
simp

lemma lemma_bh [thy_expl]: "lnull y = True \<Longrightarrow> lappend z y = z"
 by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
    (metis Llist.disc(1) lemma_ac lemma_bf)

lemma lemma_bi [thy_expl]: "lnull y = True \<Longrightarrow> lappend y z = z"
by(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  (metis Llist.disc(1) lemma_a lemma_bf)

(* Predicate for discovering conditional lemmas *)
fun sameLlength :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> bool" where
"sameLlength xs ys = (llength xs = llength ys)"

(* Zipping lazy lists *)
primcorec lzip ::  "'a Llist \<Rightarrow> 'b Llist \<Rightarrow> ('a \<times> 'b) Llist"
where
"lzip xs ys = (case xs of LNil \<Rightarrow> LNil 
                 | LCons x xss \<Rightarrow> (case ys of LNil \<Rightarrow> LNil 
                                     | LCons y yss \<Rightarrow> LCons (x,y) (lzip xss yss)
                                  )
               )"

(*cohipster sameLlength lzip*)
(* This call took around 450 seconds *)
lemma lemma_bj [thy_expl]: "llength (lzip x2 z) = llength (lzip z x2)"
  by(coinduction arbitrary: x2 z rule: Lazy_List.ENat.coinduct_strong)
    (smt ENat.sel Llist.case_eq_if lemma_aj llength.disc_iff(1) lzip.ctr(2) lzip.disc_iff(2))

lemma lemma_bk [thy_expl]: "llength (lzip y y) = llength y"
  by(coinduction arbitrary: y rule: Lazy_List.ENat.coinduct_strong)
    (smt ENat.sel Llist.collapse(2) Llist.simps(5) lemma_aj llength.disc_iff(1) lzip.ctr(2) lzip.disc_iff(2))

lemma lemma_bl [thy_expl]: "llength (lzip x2 (LCons z x4)) = llength (lzip x2 (LCons x3 x4))"
  by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
    (simp add: Llist.case_eq_if)

lemma lemma_bm [thy_expl]: "llength (lzip z (LCons y z)) = llength z"
  by(coinduction arbitrary: y z rule: Lazy_List.ENat.coinduct_strong)
    (smt ENat.sel Llist.case_eq_if Llist.collapse(2) Llist.disc(2) Llist.sel(3) lemma_aj llength.disc_iff(2) lzip.ctr(2) lzip.disc_iff(2))

lemma lemma_bn [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> llength (lzip x3 (LCons x2 LNil)) = llength (lzip (LCons x2 LNil) x3)"
  by(coinduction arbitrary: x2 x3 z rule: Lazy_List.ENat.coinduct_strong)
    (simp add: lemma_bj)

lemma lemma_bo [thy_expl]: "lzip (LCons z x3) (LCons x2 x4) = LCons (z, x2) (lzip x3 x4)"
  by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.Llist.coinduct_strong)
    simp

lemma lemma_bp [thy_expl]: "sameLlength x2 y = True \<Longrightarrow> ESuc (llength (lzip (LCons z x2) x2)) = ESuc (llength x2)"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.ENat.coinduct_strong)
    (metis Lazy_List_Cond.lemma_bj lemma_bm)

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> llength (lzip x2 z) = llength (lzip x2 x3)"
  oops

lemma unknown [thy_expl]: "equal_ENat EZ (llength y) = sameLlength y LNil"
  oops

lemma unknown [thy_expl]: "sameLlength z (LCons y x3) = sameLlength z (LCons x2 x3)"
  oops

lemma unknown [thy_expl]: "sameLlength z (LCons y z) = False"
  oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength z (LCons x2 y) = sameLlength z (LCons x2 x3)"
  oops

lemma unknown [thy_expl]: "sameLlength y (lzip x2 z) = sameLlength y (lzip z x2)"
  oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> sameLlength x2 (lzip x3 z) = sameLlength x2 (lzip x3 x4)"
  oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (llength z) = sameLlength y z"
  oops

lemma unknown [thy_expl]: "sameLlength (LCons y z) LNil = False"
  oops

lemma unknown [thy_expl]: "sameLlength LNil (lzip y y) = sameLlength y LNil"
  oops

lemma unknown [thy_expl]: "equal_ENat (ESuc EZ) (llength y) = sameLlength y (LCons z LNil)"
  oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip x2 (LCons x3 z)) = llength (lzip x2 (LCons x3 x4))"
  oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip z (LCons x2 x3)) = llength (lzip (LCons x2 x3) x4)"
  oops

lemma unknown [thy_expl]: "equal_ENat (ESuc (llength x2)) (llength y) = sameLlength y (LCons z x2)"
  oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (ESuc (llength x2)) = sameLlength y (LCons z x2)"
  oops

lemma unknown [thy_expl]: "sameLlength y (LCons x2 (LCons z x3)) = sameLlength y (LCons z (LCons x2 x3))"
  oops

lemma unknown [thy_expl]: "sameLlength x2 (LCons y (LCons z x2)) = False"
  oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (LCons x2 (LCons x3 y)) = sameLlength z (LCons x2 (LCons x3 x4))"
  oops

lemma unknown [thy_expl]: "sameLlength (LCons y x2) (LCons z x3) = sameLlength x2 x3"
  oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength (LCons z (LCons x2 x3)) x3 = False"
  oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow> sameLlength x4 (LCons z (LCons x2 y)) = sameLlength (LCons z (LCons x2 x3)) x4"
  oops

lemma unknown [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (LCons x3 (lzip x4 z)) = sameLlength x2 (LCons x3 (lzip x4 x5))"
  oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (LCons x2 (lzip y x3)) = sameLlength z (LCons x2 (lzip x3 x4))"
  oops

lemma unknown [thy_expl]: "sameLlength x2 (lzip x3 (LCons z x5)) = sameLlength x2 (lzip x3 (LCons x4 x5))"
  oops

lemma unknown [thy_expl]: "sameLlength z (lzip x2 (LCons y x2)) = sameLlength z (lzip x2 x2)"
  oops

lemma unknown [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (lzip x3 (LCons x4 z)) = sameLlength x2 (lzip x3 (LCons x4 x5))"
  oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (lzip y (LCons x2 x3)) = sameLlength z (lzip (LCons x2 x3) x4)"
  oops

lemma unknown [thy_expl]: "sameLlength (lzip z y) (lzip x2 x3) = sameLlength (lzip y z) (lzip x2 x3)"
  oops

lemma unknown [thy_expl]: "sameLlength (lzip y y) (lzip z z) = sameLlength y z"
  oops

lemma unknown [thy_expl]: "sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x6 z = True \<Longrightarrow> sameLlength (lzip x3 x2) (lzip x5 x6) = sameLlength (lzip x3 x4) (lzip x5 x6)"
  oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (llength (lzip z x2)) = sameLlength (lzip y y) (lzip z x2)"
  oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow>
                           equal_ENat (llength x3) (llength (lzip z x2)) = sameLlength (lzip z x2) (lzip x3 x3)"
  oops

lemma unknown [thy_expl]: "equal_ENat (llength (lzip y z)) (llength x2) = sameLlength (lzip y z) (lzip x2 x2)"
  oops

lemma unknown [thy_expl]: "sameLlength x2 (LCons y (LCons z LNil)) = equal_ENat (ESuc (ESuc EZ)) (llength x2)"
  oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength z (lzip x3 (LCons x2 LNil)) = sameLlength z (lzip (LCons x2 LNil) x3)"
  oops

lemma unknown [thy_expl]: "sameLlength LNil (lzip x3 (LCons z x2)) = sameLlength x3 LNil"
  oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength (lzip x3 (LCons x2 LNil)) z = sameLlength z (lzip (LCons x2 LNil) x3)"
  oops

lemma unknown [thy_expl]: "equal_ENat (ESuc (ESuc (llength x3))) (llength y) = sameLlength y (LCons z (LCons x2 x3))"
  oops

lemma unknown [thy_expl]: "equal_ENat z x = True \<Longrightarrow>
equal_ENat z (ESuc (ESuc (ESuc (ESuc y)))) = equal_ENat (ESuc (ESuc (ESuc (ESuc y)))) z"
  oops


(*cohipster sameLlength lappend lzip*)
(* Here 198 properties are discovered and the exploration and proof took about 1.5 hours *)
(* lemma ? is lzip_lappend from Coinductive_List *)
lemma lemma_bq [thy_expl]: "sameLlength x2 y = True \<Longrightarrow> llength (lappend z y) = llength (lappend z x2)"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.ENat.coinduct_strong)
    (metis lemma_aq sameLlength.elims(2))
    
lemma lemma_br [thy_expl]: "lzip z (lappend z y) = lzip z z"
  by(coinduction arbitrary: y z rule: Lazy_List.Llist.coinduct_strong)
(smt Llist.case_eq_if Llist.collapse(2) Llist.sel(1) Llist.sel(3) lappend.code lappend.disc_iff(1) lemma_bo lzip.disc_iff(2))

lemma lemma_bs [thy_expl]: "lzip (lappend z y) z = lzip z z"
  by(coinduction arbitrary: y z rule: Lazy_List.Llist.coinduct_strong)
(smt Llist.case_eq_if Llist.collapse(2) Llist.sel(1) Llist.sel(3) lappend.code lappend.disc_iff(1) lemma_bo lzip.disc_iff(2))

lemma lemma_bt [thy_expl]: "sameLlength z x2 = True \<Longrightarrow> lzip (lappend z y) x2 = lzip z x2"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
(smt ENat.sel Llist.case_eq_if Llist.collapse(2) Llist.sel(1) Llist.sel(3) lappend.ctr(2) lappend.disc_iff(1) lemma_aj lemma_bo llength.disc_iff(2) lzip.disc_iff(2) sameLlength.simps)

lemma lemma_bu [thy_expl]: "sameLlength x2 z = True \<Longrightarrow> lzip (lappend z y) x2 = lzip z x2"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
(simp add: lemma_bt)

lemma lemma_bv [thy_expl]: "sameLlength x2 z = True \<Longrightarrow> lzip z (lappend x2 y) = lzip z x2"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
(smt ENat.sel Llist.case_eq_if Llist.collapse(2) Llist.distinct(1) Llist.sel(1) Llist.sel(3) lappend.ctr(2) lemma_aj lemma_bm lemma_bo llength.disc_iff(2) lzip.code lzip.ctr(2) sameLlength.elims(2) sameLlength.elims(3))

lemma lemma_bw [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend z (lappend x2 y)) = llength (lappend z (lappend x2 x3))"
by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
  (metis (mono_tags, lifting) lemma_aq lemma_bq)
  
lemma lemma_bx [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend z (lappend x3 x2)) = llength (lappend z (lappend x2 x3))"
  by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
    (metis lemma_aq lemma_as)

lemma lemma_by [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend z (lappend y x2)) = llength (lappend z (lappend x2 x3))"
  by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
(smt lemma_aq lemma_as lemma_bq)

lemma lemma_bz [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend (lappend x3 z) x2) = llength (lappend z (lappend x2 x3))"
by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
  (metis lemma_ab lemma_as)
  
lemma lemma_ca [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend (lappend y z) x2) = llength (lappend z (lappend x2 x3))"
  by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
    (smt lemma_ab lemma_as lemma_bq)

lemma lemma_cb [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend z (lzip x3 x2)) = llength (lappend z (lzip x2 x3))"
  by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
(metis lemma_aq lemma_bj)

lemma lemma_cc [thy_expl]: "lzip (LCons z (lappend x2 y)) x2 = lzip (LCons z x2) x2"
by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
  (smt Llist.case_eq_if Llist.collapse(2) Llist.disc(2) Llist.sel(1) Llist.sel(3) lappend.code lemma_bo lzip.disc(1))
  
lemma lemma_cd [thy_expl]: "lzip (lappend y z) (lappend y x2) = lappend (lzip y y) (lzip z x2)"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
    (smt Llist.collapse(2) Llist.sel(1) Llist.sel(3) lappend.disc_iff(1) lemma_aa lemma_bi lemma_bo lzip.disc_iff(2))

lemma lemma_ce [thy_expl]: "lzip (LCons z LNil) (lappend x2 x2) = lzip (LCons z LNil) x2"
  by(coinduction arbitrary: x2 z rule: Lazy_List.Llist.coinduct_strong)
(simp add: Llist.case_eq_if lzip.ctr(1))

lemma lemma_cf [thy_expl]: "lzip (lappend z z) (LCons x2 LNil) = lzip z (LCons x2 LNil)"
by(coinduction arbitrary: x2 z rule: Lazy_List.Llist.coinduct_strong)
  (simp add: Llist.case_eq_if lzip.ctr(1))
  
lemma lemma_cg [thy_expl]: "sameLlength x2 z = True \<Longrightarrow> lzip (lappend x2 z) (LCons x3 LNil) = lzip x2 (LCons x3 LNil)"
  by(coinduction arbitrary: x2 x3 z rule: Lazy_List.Llist.coinduct_strong)
    (smt Llist.collapse(2) Llist.disc(1) Llist.simps(5) lappend.ctr(2) lappend.disc_iff(1) lemma_bo lemma_bq llength.disc_iff(1) lzip.ctr(1))

lemma lemma_ch [thy_expl]: "sameLlength z x2 = True \<Longrightarrow> lzip (lappend x2 z) (LCons x3 LNil) = lzip x2 (LCons x3 LNil)"
  by(coinduction arbitrary: x2 x3 z rule: Lazy_List.Llist.coinduct_strong)
(simp add: lemma_cg)

lemma lemma_ci [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> llength (lzip x2 z) = llength (lzip x2 x3)"
by(coinduction arbitrary: x2 x3 z rule: Lazy_List.ENat.coinduct_strong)
  (smt ENat.sel Llist.collapse(2) lemma_aj lemma_bo llength.disc_iff(2) lzip.disc_iff(2) sameLlength.elims(2) sameLlength.elims(3))
  
lemma lemma_cj [thy_expl]: "sameLlength z x2 = True \<Longrightarrow> lzip z (lappend x2 y) = lzip z x2"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
    (simp add: lemma_bv)

lemma lemma_ck [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lappend x2 (lzip x3 z)) = llength (lappend x2 (lzip x3 x4))"
  by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
(metis (full_types) lemma_aq lemma_ci)

lemma lemma_cl [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> llength (lappend z (lzip y x2)) = llength (lappend z (lzip x2 x3))"
  by(coinduction arbitrary: x2 x3 y z rule: Lazy_List.ENat.coinduct_strong)
(metis (mono_tags, lifting) Lazy_List_Cond.lemma_ci lemma_aq lemma_bj)

lemma lemma_cm [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip x2 (LCons x3 z)) = llength (lzip x2 (LCons x3 x4))"
by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
  (smt Llist.collapse(2) lemma_aj lemma_bo lemma_ci llength.disc(1) lzip.disc_iff(2))
  
lemma lemma_cn [thy_expl]: "llength (lzip z (lappend x3 x2)) = llength (lzip z (lappend x2 x3))"
  by(coinduction arbitrary: x2 x3 z rule: Lazy_List.ENat.coinduct_strong)
    (metis lemma_as lemma_ci sameLlength.simps)

lemma lemma_co [thy_expl]: "llength (lzip z (lappend y z)) = llength z"
  by(coinduction arbitrary: y z rule: Lazy_List.ENat.coinduct_strong)
(metis Lazy_List_Cond.lemma_cn lemma_bk lemma_br)

lemma lemma_cp [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip x2 (lappend x3 z)) = llength (lzip x2 (lappend x3 x4))"
by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
  (smt Lazy_List_Cond.lemma_bq lemma_ci sameLlength.simps)
  
lemma lemma_cq [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip z (LCons x2 x3)) = llength (lzip (LCons x2 x3) x4)"
  by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
    (metis lemma_bj lemma_ci)

lemma lemma_cr [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> llength (lzip z (lappend x2 x3)) = llength (lzip (lappend x2 x3) x4)"
  by(coinduction arbitrary: x2 x3 x4 z rule: Lazy_List.ENat.coinduct_strong)
(metis lemma_bj lemma_ci)

lemma lemma_cs [thy_expl]: "lzip x2 (LCons z (lappend x2 y)) = lzip x2 (LCons z x2)"
  by(coinduction arbitrary: x2 y z rule: Lazy_List.Llist.coinduct_strong)
(smt Llist.collapse(2) Llist.disc(2) Llist.sel(1) Llist.sel(3) lemma_aa lemma_bo lzip.disc(1))

lemma lemma_ct [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (LCons x3 (lzip x4 z)) = sameLlength x2 (LCons x3 (lzip x4 x5))"
apply (induct x2 arbitrary: x3 x4 x5 z)
  apply (metis (no_types, lifting) lemma_aj lemma_ci sameLlength.elims(2) sameLlength.elims(3))
done
    
lemma lemma_cu [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (LCons x2 (lzip y x3)) = sameLlength z (LCons x2 (lzip x3 x4))"
  apply (induct x3 arbitrary: x2 x4 y z)
  apply (smt Lazy_List_Cond.lemma_ci lemma_aj lemma_bj sameLlength.simps)
done
  
lemma lemma_cv [thy_expl]: "sameLlength x2 y = True \<Longrightarrow> ESuc (llength (lzip (lappend z x2) x2)) = ESuc (llength x2)"
by(coinduction arbitrary: x2 y z rule: Lazy_List.ENat.coinduct_strong)
  (metis lemma_bj lemma_co)
  
lemma unknown [thy_expl]: "equal_ENat EZ (llength y) = sameLlength y LNil"
  oops
    
lemma unknown [thy_expl]: "sameLlength z (LCons y x3) = sameLlength z (LCons x2 x3)"
  oops
    
lemma unknown [thy_expl]: "sameLlength z (LCons y z) = False"
  oops
    
lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength z (LCons x2 y) = sameLlength z (LCons x2 x3)"
  oops
  
lemma unknown [thy_expl]: "sameLlength y (lappend x2 z) = sameLlength y (lappend z x2)"
oops
  
lemma unknown [thy_expl]: "sameLlength y (lappend y z) = sameLlength z LNil"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend z y) = sameLlength z LNil"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength z (lappend x2 y) = sameLlength z (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength y (lzip x2 z) = sameLlength y (lzip z x2)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow> sameLlength x2 (lzip x3 z) = sameLlength x2 (lzip x3 x4)"
oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (llength z) = sameLlength y z"
oops

lemma unknown [thy_expl]: "sameLlength (LCons y z) LNil = False"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lappend y y) = sameLlength y LNil"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lzip y y) = sameLlength y LNil"
oops

lemma unknown [thy_expl]: "equal_ENat (ESuc EZ) (llength y) = sameLlength y (LCons z LNil)"
oops

lemma unknown [thy_expl]: "equal_ENat (ESuc (llength x2)) (llength y) = sameLlength y (LCons z x2)"
oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (ESuc (llength x2)) = sameLlength y (LCons z x2)"
oops

lemma unknown [thy_expl]: "lzip x2 (lappend z (lappend x2 y)) = lzip x2 (lappend z x2)"
oops

lemma unknown [thy_expl]: "sameLlength x2 x3 = True \<Longrightarrow> lzip (LCons z (lappend x2 y)) x3 = lzip (LCons z x2) x3"
oops

lemma unknown [thy_expl]: "sameLlength x3 x2 = True \<Longrightarrow> lzip (LCons z (lappend x2 y)) x3 = lzip (LCons z x2) x3"
oops

lemma unknown [thy_expl]: "lzip (lappend z (lappend x2 y)) x2 = lzip (lappend z x2) x2"
oops

lemma unknown [thy_expl]: "sameLlength x2 x3 = True \<Longrightarrow> lzip (lappend z (lappend x2 y)) x3 = lzip (lappend z x2) x3"
oops

lemma unknown [thy_expl]: "sameLlength x3 x2 = True \<Longrightarrow> lzip (lappend z (lappend x2 y)) x3 = lzip (lappend z x2) x3"
oops

lemma unknown [thy_expl]: "sameLlength x3 x4 = True \<Longrightarrow>
                           sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x4) x3) x5 = lzip (lappend (lappend x3 x3) x4) x5"
oops

lemma unknown [thy_expl]: "sameLlength x3 x4 = True \<Longrightarrow>
                           sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow> lzip (lappend (lappend x3 x4) x3) x5 = lzip (lappend (lappend x3 x3) x4) x5"
oops

lemma unknown [thy_expl]: "sameLlength x3 x5 = True \<Longrightarrow>
                           sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x4) x3) x5 = lzip (lappend (lappend x3 x3) x4) x5"
oops

lemma unknown [thy_expl]: "sameLlength x3 x5 = True \<Longrightarrow>
                           sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow> lzip (lappend (lappend x3 x4) x3) x5 = lzip (lappend (lappend x3 x3) x4) x5"
oops

lemma unknown [thy_expl]: "sameLlength x3 x4 = True \<Longrightarrow>
                           sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x3 x4 = True \<Longrightarrow>
                           sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x5 z = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x5 z = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x6 x3 = True \<Longrightarrow> lzip (lappend (lappend x5 x5) x4) x6 = lzip (lappend (lappend x5 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x3 x6 = True \<Longrightarrow> lzip (lappend (lappend x5 x5) x4) x6 = lzip (lappend (lappend x5 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength z x5 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip (lappend (lappend x3 x5) x4) x6 = lzip (lappend (lappend x3 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow>
                           sameLlength x6 x3 = True \<Longrightarrow> lzip (lappend (lappend x4 x5) x4) x6 = lzip (lappend (lappend x4 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow>
                           sameLlength x3 x6 = True \<Longrightarrow> lzip (lappend (lappend x4 x5) x4) x6 = lzip (lappend (lappend x4 x4) x5) x6"
oops

lemma unknown [thy_expl]: "sameLlength y z = True \<Longrightarrow> lzip (lappend y x2) (lappend z x3) = lappend (lzip y z) (lzip x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength z y = True \<Longrightarrow> lzip (lappend y x2) (lappend z x3) = lappend (lzip y z) (lzip x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow> lzip z (LCons x2 (lappend x3 y)) = lzip z (LCons x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow> lzip z (lappend x2 (lappend x3 y)) = lzip z (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x4 x5 = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x5) x4) = lzip x3 (lappend (lappend x4 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x4 x6 = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x5) x4) = lzip x3 (lappend (lappend x4 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x4 x5 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x5 x4 = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow>
                           sameLlength x5 x3 = True \<Longrightarrow> lzip x4 (lappend (lappend x6 x6) x5) = lzip x4 (lappend (lappend x6 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x5 x4 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow>
                           sameLlength x3 x6 = True \<Longrightarrow> lzip x4 (lappend (lappend x5 x6) x5) = lzip x4 (lappend (lappend x5 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> lzip z (LCons x2 (lappend x3 y)) = lzip z (LCons x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> lzip z (lappend x2 (lappend x3 y)) = lzip z (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x4 x5 = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x5) x4) = lzip x3 (lappend (lappend x4 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x4 x6 = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x5) x4) = lzip x3 (lappend (lappend x4 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x4 x5 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x5 x4 = True \<Longrightarrow>
                           sameLlength x6 x2 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow>
                           sameLlength x5 x3 = True \<Longrightarrow> lzip x4 (lappend (lappend x6 x6) x5) = lzip x4 (lappend (lappend x6 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x5 x4 = True \<Longrightarrow>
                           sameLlength x2 x6 = True \<Longrightarrow> lzip x3 (lappend (lappend x4 x6) x5) = lzip x3 (lappend (lappend x4 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength z x4 = True \<Longrightarrow>
                           sameLlength x2 x5 = True \<Longrightarrow>
                           sameLlength x3 x6 = True \<Longrightarrow> lzip x4 (lappend (lappend x5 x6) x5) = lzip x4 (lappend (lappend x5 x5) x6)"
oops

lemma unknown [thy_expl]: "sameLlength y (LCons x2 (LCons z x3)) = sameLlength y (LCons z (LCons x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength x2 (LCons y (LCons z x2)) = False"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (LCons x2 (LCons x3 y)) = sameLlength z (LCons x2 (LCons x3 x4))"
oops

lemma unknown [thy_expl]: "sameLlength y (LCons z (lappend x3 x2)) = sameLlength y (LCons z (lappend x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength z (LCons y (lappend z x2)) = False"
oops

lemma unknown [thy_expl]: "sameLlength x2 (LCons y (lappend z x2)) = False"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (LCons x2 (lappend x3 y)) = sameLlength z (LCons x2 (lappend x3 x4))"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend x2 (LCons z x3)) = sameLlength y (LCons z (lappend x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend z (lappend x3 x2)) = sameLlength y (lappend z (lappend x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend x2 (lappend z x3)) = sameLlength y (lappend z (lappend x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength z (lappend z (lappend y x2)) = sameLlength z (lappend y (lappend z x2))"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend z (lappend x2 y)) = sameLlength LNil (lappend z x2)"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow>
                           sameLlength z (lappend x2 (lappend x3 y)) = sameLlength z (lappend x2 (lappend x3 x4))"
oops

lemma unknown [thy_expl]: "sameLlength (LCons y x2) (LCons z x3) = sameLlength x2 x3"
oops

lemma unknown [thy_expl]: "sameLlength (LCons y x2) (lappend x3 x4) = sameLlength (LCons z x2) (lappend x3 x4)"
oops

lemma unknown [thy_expl]: "sameLlength (LCons x2 y) (lappend y z) = sameLlength z (LCons x2 LNil)"
oops

lemma unknown [thy_expl]: "sameLlength (LCons x2 y) (lappend z y) = sameLlength z (LCons x2 LNil)"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength (LCons z (LCons x2 x3)) x3 = False"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength (LCons z (lappend x2 x3)) x3 = False"
oops

lemma unknown [thy_expl]: "sameLlength x3 x2 = True \<Longrightarrow> sameLlength x2 y = True \<Longrightarrow> sameLlength (LCons z (lappend x3 x2)) x3 = False"
oops

lemma unknown [thy_expl]: "sameLlength x3 x2 = True \<Longrightarrow>
                           sameLlength x2 y = True \<Longrightarrow> sameLlength (LCons z x3) (lappend x2 x2) = sameLlength (LCons z x2) (lappend x3 x3)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x5 y = True \<Longrightarrow>
                           sameLlength (LCons x2 z) (lappend x4 x5) = sameLlength (LCons x2 x3) (lappend x4 x5)"
oops

lemma unknown [thy_expl]: "sameLlength (lappend z y) (lappend x2 x3) = sameLlength (lappend y z) (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength (lappend z y) (lappend x2 y) = sameLlength z x2"
oops

lemma unknown [thy_expl]: "sameLlength (lappend z y) (lappend y x3) = sameLlength (lappend z x2) (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength (lappend z y) (lappend x3 y) = sameLlength (lappend z x2) (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength (lappend y z) (lappend z x2) = sameLlength (lappend z y) (lappend z x2)"
oops

lemma unknown [thy_expl]: "sameLlength (lappend y y) (lappend z z) = sameLlength y z"
oops

lemma unknown [thy_expl]: "sameLlength z y = True \<Longrightarrow> sameLlength (lappend x2 (lappend x3 z)) z = sameLlength LNil (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow> sameLlength (lappend x2 (lappend z x3)) z = sameLlength LNil (lappend x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow>
                           sameLlength x5 y = True \<Longrightarrow>
                           sameLlength (lappend x2 z) (lappend x4 x5) = sameLlength (lappend x2 x3) (lappend x4 x5)"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow>
                           sameLlength x3 x2 = True \<Longrightarrow>
                           sameLlength x2 y = True \<Longrightarrow>
                           sameLlength (lappend (lappend z x3) x2) x3 = sameLlength (lappend (lappend x3 z) x2) x3"
oops

lemma unknown [thy_expl]: "sameLlength z x2 = True \<Longrightarrow>
                           sameLlength x2 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow>
                           sameLlength (lappend (lappend z z) z) x2 = sameLlength (lappend (lappend x3 z) x2) x3"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow> sameLlength x4 (LCons z (LCons x2 y)) = sameLlength (LCons z (LCons x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow> sameLlength x4 (LCons z (lappend x2 y)) = sameLlength (LCons z (lappend x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow> sameLlength x4 (LCons z (lappend x3 x2)) = sameLlength (LCons z (lappend x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength x4 (lappend x2 (LCons z x3)) = sameLlength (LCons z (lappend x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow>
                           sameLlength x4 (lappend z (lappend x2 y)) = sameLlength (lappend z (lappend x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength x4 x3 = True \<Longrightarrow>
                           sameLlength x3 y = True \<Longrightarrow>
                           sameLlength x4 (lappend z (lappend x3 x2)) = sameLlength (lappend z (lappend x2 x3)) x4"
oops

lemma unknown [thy_expl]: "sameLlength y (lappend z (lzip x3 x2)) = sameLlength y (lappend z (lzip x2 x3))"
oops

lemma unknown [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (lappend x3 (lzip x4 z)) = sameLlength x2 (lappend x3 (lzip x4 x5))"
oops

lemma unknown [thy_expl]: "sameLlength x2 (lzip x3 (LCons z x5)) = sameLlength x2 (lzip x3 (LCons x4 x5))"
oops

lemma unknown [thy_expl]: "sameLlength z (lzip x2 (LCons y x2)) = sameLlength z (lzip x2 x2)"
oops

lemma unknown [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (lzip x3 (LCons x4 z)) = sameLlength x2 (lzip x3 (LCons x4 x5))"
oops

lemma unknown [thy_expl]: "sameLlength z (lzip x2 (lappend x4 x3)) = sameLlength z (lzip x2 (lappend x3 x4))"
oops

lemma unknown [thy_expl]: "sameLlength z (lzip x2 (lappend y x2)) = sameLlength z (lzip x2 x2)"
oops

lemma unknown [thy_expl]: "sameLlength x5 z = True \<Longrightarrow> sameLlength x2 (lzip x3 (lappend x4 z)) = sameLlength x2 (lzip x3 (lappend x4 x5))"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (lzip y (LCons x2 x3)) = sameLlength z (lzip (LCons x2 x3) x4)"
oops

lemma unknown [thy_expl]: "sameLlength x4 y = True \<Longrightarrow> sameLlength z (lzip y (lappend x2 x3)) = sameLlength z (lzip (lappend x2 x3) x4)"
oops

lemma unknown [thy_expl]: "sameLlength (lzip z y) (lzip x2 x3) = sameLlength (lzip y z) (lzip x2 x3)"
oops

lemma unknown [thy_expl]: "sameLlength (lzip y y) (lzip z z) = sameLlength y z"
oops

lemma unknown [thy_expl]: "sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x6 z = True \<Longrightarrow> sameLlength (lzip x3 x2) (lzip x5 x6) = sameLlength (lzip x3 x4) (lzip x5 x6)"
oops

lemma unknown [thy_expl]: "equal_ENat (llength y) (llength (lzip z x2)) = sameLlength (lzip y y) (lzip z x2)"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow>
                           equal_ENat (llength x3) (llength (lzip z x2)) = sameLlength (lzip z x2) (lzip x3 x3)"
oops

lemma unknown [thy_expl]: "equal_ENat (llength (lzip y z)) (llength x2) = sameLlength (lzip y z) (lzip x2 x2)"
oops

lemma unknown [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> lzip (LCons x2 LNil) (lappend x3 z) = lzip (LCons x2 LNil) x3"
oops

lemma unknown [thy_expl]: "sameLlength z x3 = True \<Longrightarrow> lzip (LCons x2 LNil) (lappend x3 z) = lzip (LCons x2 LNil) x3"
oops

lemma unknown [thy_expl]: "sameLlength x2 (LCons y (LCons z LNil)) = equal_ENat (ESuc (ESuc EZ)) (llength x2)"
oops

lemma unknown [thy_expl]: "sameLlength (LCons y LNil) (lappend z z) = False"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lappend y (lappend y z)) = sameLlength LNil (lappend y z)"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lappend y (lappend z z)) = sameLlength LNil (lappend y z)"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength z (lzip x3 (LCons x2 LNil)) = sameLlength z (lzip (LCons x2 LNil) x3)"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lzip x3 (LCons z x2)) = sameLlength x3 LNil"
oops

lemma unknown [thy_expl]: "sameLlength LNil (lzip z (lappend x2 x2)) = sameLlength LNil (lzip z x2)"
oops

lemma unknown [thy_expl]: "sameLlength x2 y = True \<Longrightarrow> sameLlength LNil (lzip (lappend z x2) x2) = sameLlength LNil x2"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength LNil (lzip x4 (lappend x2 x3)) = sameLlength LNil (lzip (lappend x2 x3) x4)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow>
                           sameLlength LNil (lzip x5 (lappend x3 x4)) = sameLlength LNil (lzip (lappend x3 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength x4 x2 = True \<Longrightarrow>
                           sameLlength x5 z = True \<Longrightarrow>
                           sameLlength LNil (lzip x5 (lappend x3 x2)) = sameLlength LNil (lzip (lappend x3 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength x5 x2 = True \<Longrightarrow>
                           sameLlength LNil (lzip x5 (lappend x4 x3)) = sameLlength LNil (lzip (lappend x3 x4) x5)"
oops

lemma unknown [thy_expl]: "sameLlength x3 y = True \<Longrightarrow> sameLlength (lzip x3 (LCons x2 LNil)) z = sameLlength z (lzip (LCons x2 LNil) x3)"
oops

lemma unknown [thy_expl]: "sameLlength x4 z = True \<Longrightarrow>
                           sameLlength (lzip x4 (lappend x2 x3)) LNil = sameLlength LNil (lzip (lappend x2 x3) x4)"
oops

lemma unknown [thy_expl]: "equal_ENat (ESuc (ESuc (llength x3))) (llength y) = sameLlength y (LCons z (LCons x2 x3))"
oops

end