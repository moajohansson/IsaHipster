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
lemma lemma_bj [thy_expl]: "lzip (LCons z x3) (LCons x2 x4) = LCons (z, x2) (lzip x3 x4)"
  by(coinduction arbitrary: x2 x3 x4 z rule: Llist.coinduct_strong)
simp

lemma lemma_bk [thy_expl]: "llength (lzip x2 z) = llength (lzip z x2)"
by(coinduction arbitrary: x2 z rule: ENat.coinduct_strong)
(smt ENat.sel Lazy_List_Cond.lemma_bj Llist.collapse(2) lemma_aj llength.disc_iff(2) lzip.disc_iff(2))

lemma lemma_bl [thy_expl]: "llength (lzip y y) = llength y"
  by(coinduction arbitrary: y rule: ENat.coinduct_strong)
(smt ENat.sel Lazy_List_Cond.lemma_bj Llist.collapse(2) lemma_aj llength.disc_iff(2) lzip.disc_iff(2))

lemma lemma_bm [thy_expl]: "llength (lzip x2 (LCons z x4)) = llength (lzip x2 (LCons x3 x4))"
 by(coinduction arbitrary: x2 x3 x4 z rule: ENat.coinduct_strong)
    (smt Lazy_List_Cond.lemma_bj Llist.collapse(2) lemma_aj llength.disc(1) lzip.disc_iff(2))

lemma lemma_bn [thy_expl]: "llength (lzip z (LCons y z)) = llength z"
 by(coinduction arbitrary: y z rule: ENat.coinduct_strong)
    (metis ENat.sel Lazy_List_Cond.lemma_bj Llist.collapse(2) Llist.disc(2) lemma_aj llength.disc_iff(2) lzip.disc_iff(2))

lemma lemma_bo [thy_expl]: "sameLlength x3 z = True \<Longrightarrow> llength (lzip x3 (LCons x2 LNil)) = llength (lzip (LCons x2 LNil) x3)"
 by(coinduction arbitrary: x2 x3 z rule: ENat.coinduct_strong)
    (metis lemma_bk)

lemma lemma_bp [thy_expl]: "sameLlength x2 y = True \<Longrightarrow> ESuc (llength (lzip (LCons z x2) x2)) = ESuc (llength x2)"
 by(coinduction arbitrary: x2 y z rule: ENat.coinduct_strong)
    (metis Lazy_List.lemma_bk lemma_bn)

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

(*cohipster sameLlength lappend lzip*)
(* Here 206 properties are discovered and the exploration and proof took about 3 hours *)
(* lemma ? is lzip_lappend from Coinductive_List *)

end