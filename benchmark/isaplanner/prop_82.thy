theory prop_82
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => (('a, 'b) Pair2) list" where
  "zip (Nil2) y = Nil2"
  | "zip (Cons2 z x2) (Nil2) = Nil2"
  | "zip (Cons2 z x2) (Cons2 x3 x4) = Cons2 (Pair z x3) (zip x2 x4)"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  (*hipster zip take *)

datatype NPair = Pairn Nat Nat
datatype PList = PNil | PCons NPair PList
datatype Nlist = NNil | NCons Nat Nlist

fun ptake :: "Nat => PList => PList" where
"ptake Z     xs           = PNil"
| "ptake (S _) PNil         = PNil"
| "ptake (S n) (PCons x xs) = PCons x (ptake n xs)"
  fun ntake :: "Nat => Nlist => Nlist" where
  "ntake (Z) y = NNil"
  | "ntake (S z) (NNil) = NNil"
  | "ntake (S z) (NCons x2 x3) = NCons x2 (ntake z x3)"
  fun pzip :: "Nlist => Nlist => PList" where
  "pzip (NNil) y = PNil"
  | "pzip (NCons z x2) (NNil) = PNil"
  | "pzip (NCons z x2) (NCons x3 x4) = PCons (Pairn z x3) (pzip x2 x4)"


lemma lemma_ai [thy_expl]: "take x3 Nil2 = Nil2"
by (hipster_induct_schemes take.simps)

lemma lemma_aj [thy_expl]: "take x3 (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma lemma_ak [thy_expl]: "take (S x3) (take x3 y3) = take x3 y3"
by (hipster_induct_schemes take.simps)

lemma lemma_ab [thy_expl]: "zip Nil2 x1 = zip x1 Nil2"
by (hipster_induct_schemes zip.simps)

lemma lemma_ac [thy_expl]: "zip Nil2 x1 = zip y1 Nil2"
by (hipster_induct_schemes zip.simps)

(*hipster ptake ntake pzip*)
lemma lemma_a [thy_expl]: "pzip x1 NNil = PNil"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_aa [thy_expl]: "ntake x1 NNil = NNil"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_ad [thy_expl]: "ptake x1 PNil = PNil"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_ae [thy_expl]: "ntake x2 (ntake x2 y2) = ntake x2 y2"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_af [thy_expl]: "ptake x2 (ptake x2 y2) = ptake x2 y2"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_ag [thy_expl]: "ptake x19 (pzip y19 y19) = pzip y19 (ntake x19 y19)"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_ah [thy_expl]: "pzip (ntake x19 y19) y19 = pzip y19 (ntake x19 y19)"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_al [thy_expl]: "pzip (ntake x19 y19) (ntake x19 y19) = pzip y19 (ntake x19 y19)"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_am [thy_expl]: "ntake (S x2) (ntake x2 y2) = ntake x2 y2"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma lemma_an [thy_expl]: "ptake (S x2) (ptake x2 y2) = ptake x2 y2"
by (hipster_induct_schemes ptake.simps ntake.simps pzip.simps)

lemma unknown [thy_expl]: "ntake x (ntake y z) = ntake y (ntake x z)"
oops

setup{*Hip_Tac_Ops.set_metis_to @{context} 10000*}
setup{*Hip_Tac_Ops.set_metis_filter @{context} (K false)*}

lemma lemma_ao [thy_expl]: "ptake x (pzip y z) = pzip y (ntake x z)"
by (hipster_induct_schemes thy_expl PList.exhaust Nat.exhaust Nlist.exhaust ntake.simps ptake.simps pzip.simps)
(*
apply(induction y z arbitrary: x  rule: pzip.induct)
apply simp_all
apply (metis  PList.exhaust Nat.exhaust Nlist.exhaust ntake.simps ptake.simps pzip.simps)
apply (metis  PList.exhaust Nat.exhaust Nlist.exhaust ntake.simps ptake.simps pzip.simps)
apply (metis PList.exhaust Nat.exhaust Nlist.exhaust ntake.simps ptake.simps pzip.simps)
done*)
(*
 \<And>x. ptake x PNil = PNil
 2. \<And>z x2 x. ptake x PNil = pzip (NCons z x2) (ntake x NNil)
 3. \<And>z x2 x3 x4 x. (\<And>x. ptake x (pzip x2 x4) = pzip x2 (ntake x x4)) \<Longrightarrow> ptake x (PCons (Pairn z x3) (pzip x2 x4)) = pzip (NCons z x2) (ntake x (NCons x3 x4))

 1. \<And>z x2 x. ptake x PNil = pzip (NCons z x2) (ntake x NNil)
 2. \<And>z x2 x3 x4 x. (\<And>x. ptake x (pzip x2 x4) = pzip x2 (ntake x x4)) \<Longrightarrow> ptake x (PCons (Pairn z x3) (pzip x2 x4)) = pzip (NCons z x2) (ntake x (NCons x3 x4)

 1. \<And>z x2 x3 x4 x. (\<And>x. ptake x (pzip x2 x4) = pzip x2 (ntake x x4)) \<Longrightarrow> ptake x (PCons (Pairn z x3) (pzip x2 x4)) = pzip (NCons z x2) (ntake x (NCons x3 x4)) 

*)

setup{*Hip_Tac_Ops.set_metis_filter @{context} (K true)*}


lemma unknown [thy_expl]: "ptake x (ptake y z) = ptake y (ptake x z)"
oops

lemma unknown [thy_expl]: "pzip (ntake x y) z = pzip y (ntake x z)"
oops

lemma unknown [thy_expl]: "pzip (ntake x y) (ntake z xa) = pzip (ntake z y) (ntake x xa)"
oops

lemma unknown [thy_expl]: "pzip (ntake x y) (ntake x z) = pzip y (ntake x z)"

oops

lemma unknown [thy_expl]: "pzip (ntake x y) (ntake z y) = pzip (ntake z y) (ntake x y)"
oops

ML {* Induct.find_casesT @{context} @{typ "Nat"} *}
thm Nat.cases
thm Nat.exhaust
thm Nat.inject
thm Nat.distinct

  theorem x0 :
    "(ptake n (pzip xs ys)) = (pzip (ntake n xs) (ntake n ys))"
    apply(induction xs ys arbitrary: n rule: pzip.induct)
    apply(simp_all)
    apply(metis ptake.simps pzip.simps ntake.simps thy_expl)
    apply(metis pzip.simps take.simps ntake.simps ptake.simps NPair.exhaust Nat.exhaust PList.exhaust Nlist.exhaust)
    apply(case_tac n)
    apply simp_all
    done

fun len :: "Nlist \<Rightarrow> Nat" where
"len NNil = Z"
| "len (NCons _ xs) = S (len xs)"
  fun append :: "Nlist => Nlist => Nlist" where
  "append (NNil) y = y"
  | "append (NCons z xs) y = NCons z (append xs y)"
  fun rev :: "Nlist => Nlist" where
  "rev (NNil) = NNil"
  | "rev (NCons y xs) = append (rev xs) (NCons y (NNil))"
  fun pappend :: "PList => PList => PList" where
  "pappend (PNil) y = y"
  | "pappend (PCons z xs) y = PCons z (pappend xs y)"
  fun prev :: "PList => PList" where
  "prev (PNil) = PNil"
  | "prev (PCons y xs) = pappend (prev xs) (PCons y (PNil))"

  theorem x1 :
    "((len xs) = (len ys)) ==>
       ((pzip (rev xs) (rev ys)) = (prev (pzip xs ys)))"
       apply(induction xs ys rule: pzip.induct)
       apply simp
       apply simp
       apply simp+
sledgehammer
       apply(metis pzip.simps prev.simps pappend.simps append.simps rev.simps)

    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
