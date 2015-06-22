theory prop_85b
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
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

  fun len :: "Nlist => Nat" where
  "len (NNil) = Z"
  | "len (NCons y xs) = S (len xs)"
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

  (*hipster pzip len append rev *)
  (*hipster rev*)
lemma lemma_a [thy_expl]: "append x2 NNil = x2"
by (hipster_induct_schemes rev.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes rev.simps)

lemma lemma_ab [thy_expl]: "append (rev x5) (rev y5) = rev (append y5 x5)"
by (hipster_induct_schemes rev.simps)

(*hipster len pzip*)
lemma lemma_ac [thy_expl]: "pzip NNil x1 = pzip x1 NNil"
by (hipster_induct_schemes len.simps pzip.simps)

lemma lemma_ad [thy_expl]: "pzip NNil x1 = pzip y1 NNil"
by (hipster_induct_schemes len.simps pzip.simps)


(*hipster rev pzip*)
lemma lemma_ae [thy_expl]: "pzip x2 (append x2 y2) = pzip x2 x2"
by (hipster_induct_schemes rev.simps pzip.simps)

lemma lemma_af [thy_expl]: "pzip (append x1 y1) x1 = pzip x1 x1"
by (hipster_induct_schemes rev.simps pzip.simps)


(*hipster pzip append*)
lemma lemma_ah [thy_expl]: "pzip (append x4 x4) (NCons y4 NNil) = pzip x4 (NCons y4 NNil)"
by (hipster_induct_schemes pzip.simps append.simps)

lemma lemma_ai [thy_expl]: "pzip (NCons x1 NNil) (append y1 y1) = pzip (NCons x1 NNil) y1"
by (hipster_induct_schemes pzip.simps append.simps)

(*hipster len rev append*)
lemma lemma_aj [thy_expl]: "rev (rev x3) = x3"
by (hipster_induct_schemes len.simps rev.simps append.simps)

(*hipster prev pappend*)
lemma lemma_ag [thy_expl]: "pappend x2 PNil = x2"
by (hipster_induct_schemes prev.simps pappend.simps)

lemma lemma_ak [thy_expl]: "pappend (pappend x1 y1) z1 = pappend x1 (pappend y1 z1)"
by (hipster_induct_schemes prev.simps pappend.simps)

lemma lemma_al [thy_expl]: "pappend (prev x9) (prev y9) = prev (pappend y9 x9)"
by (hipster_induct_schemes prev.simps pappend.simps)

lemma lemma_am [thy_expl]: "prev (prev x8) = x8"
by (hipster_induct_schemes prev.simps pappend.simps)

lemma unknown []: "pzip (append x y) (rev x) = pzip x (rev x)"
oops

lemma unknown []: "pzip (rev x) (append x y) = pzip (rev x) x"
oops

(*hipster len rev append pzip*)
(*lemma lemma_ag [thy_expl]: "len (append x4 y4) = len (append y4 x4)"
by (hipster_induct_schemes len.simps rev.simps append.simps pzip.simps Nat.exhaust)*)

lemma unknown []: "pzip (append x y) (rev x) = pzip x (rev x)"
oops

lemma unknown []: "pzip (rev x) (append x y) = pzip (rev x) x"
oops

lemma unknown []: "pzip (append x x) (rev x) = pzip x (rev x)"
oops

lemma unknown []: "pzip (rev x) (append x x) = pzip (rev x) x"
oops

(*hipster pzip pappend prev rev append len*)
lemma lemma_an [thy_expl]: "pappend (pzip x1 x1) (pzip y1 z1) = pzip (append x1 y1) (append x1 z1)"
by (hipster_induct_schemes pzip.simps pappend.simps prev.simps rev.simps append.simps len.simps)

lemma unknown [thy_expl]: "len (append x y) = len (append y x)"
oops

lemma unknown [thy_expl]: "len (rev x) = len x"
oops

lemma unknown [thy_expl]: "pzip (append x y) (rev x) = pzip x (rev x)"
oops

lemma unknown [thy_expl]: "pzip (rev x) (append x y) = pzip (rev x) x"
oops

lemma unknown [thy_expl]: "pzip (append x x) (rev x) = pzip x (rev x)"
oops

lemma unknown [thy_expl]: "pzip (rev x) (append x x) = pzip (rev x) x"
oops

lemma unknown [thy_expl]: "pzip (rev x) (rev x) = prev (pzip x x)"
oops

(*hipster len *)

fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"


(*hipster equal2*)
lemma lemma_ao [thy_expl]: "equal2 x2 y2 = equal2 y2 x2"
by (hipster_induct_schemes equal2.simps)

lemma lemma_ap [thy_expl]: "equal2 x2 x2 = True"
by (hipster_induct_schemes equal2.simps)

lemma lemma_aq [thy_expl]: "equal2 x2 (S x2) = False"
by (hipster_induct_schemes equal2.simps)

(*hipster_cond equal2 len*)
lemma lemma_ar [thy_expl]: "equal2 y2 x2 \<Longrightarrow> x2 = y2"
by (hipster_induct_schemes equal2.simps len.simps)

(*hipster pappend prev pzip append rev len*)
lemma lemma_aw [thy_expl]: "pappend (pzip x1 x1) (pzip y1 z1) = pzip (append x1 y1) (append x1 z1)"
by (hipster_induct_schemes pappend.simps prev.simps pzip.simps append.simps rev.simps len.simps)

lemma unknown [thy_expl]: "len (append x y) = len (append y x)"
oops

lemma unknown [thy_expl]: "len (rev x) = len x"
oops

lemma unknown [thy_expl]: "pzip (append x y) (rev x) = pzip x (rev x)"
oops

lemma unknown [thy_expl]: "pzip (rev x) (append x y) = pzip (rev x) x"
oops

lemma unknown [thy_expl]: "pzip (append x x) (rev x) = pzip x (rev x)"
oops

lemma unknown [thy_expl]: "pzip (rev x) (append x x) = pzip (rev x) x"
oops

lemma unknown [thy_expl]: "pzip (rev x) (rev x) = prev (pzip x x)"
oops

(*hipster append len*)
(*
lemma xx[thy_expl]: "len (append xs (NCons y ys)) = S (len (append xs ys))"
by (hipster_induct_schemes append.simps len.simps list.exhaust)

lemma lemma_applen [thy_expl]: "len (append x y) = len (append y x)"
by (hipster_induct_schemes append.simps len.simps list.exhaust)*)
(*
apply(induction x y rule: pzip.induct)
apply(simp_all)
apply(metis thy_expl append.simps len.simps list.exhaust)
apply(metis thy_expl pzip.simps append.simps len.simps list.exhaust)
apply(metis (full_types) thy_expl pzip.simps append.simps len.simps list.exhaust)
by (hipster_induct_schemes append.simps len.simps list.exhaust)*)
(*
lemma lemma_at [thy_expl]: "len (rev x3) = len x3"
by (hipster_induct_schemes len.simps rev.simps append.simps)
*)
(*
len (x++y) == len (y++x) proved by induction on  y, x

zip (x++y) (rev x) == zip x (rev x) failed to be proved
zip (rev x) (x++y) == zip (rev x) x failed to be proved

zip x x++++zip y z == zip (x++y) (x++z) proved by induction on  x

zip (rev x) (rev x) == prev (zip x x) proved by induction on  x

zip (x++y) (rev x) == zip x (rev x) failed to be proved
zip (rev x) (x++y) == zip (rev x) x failed to be proved
zip (rev x) (x++x) == zip (rev x) x failed to be proved
zip (x++x) (rev x) == zip x (rev x) failed to be proved

prop_85 failed to be proved

*)

fun lenq:: "Nlist \<Rightarrow> Nlist \<Rightarrow> bool" where
"lenq xs ys = equal2 (len xs) (len ys)"


hipster lenq equal2 append

(*hipster_cond lenq rev equal2 append prev pappend*)

  theorem x0 :
    "((len xs) = (len ys)) ==>
       ((pzip (rev xs) (rev ys)) = (prev (pzip xs ys)))"
       apply(induction xs)
       apply(simp)
       apply(case_tac ys)
       apply simp

       sledgehammer


       (*by (hipster_induct_schemes len.simps pzip.simps rev.simps prev.simps pappend.simps append.simps PList.exhaust Nlist.exhaust)*)

(*
    apply(induction xs ys rule: pzip.induct)
apply simp_all
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})*)
end
