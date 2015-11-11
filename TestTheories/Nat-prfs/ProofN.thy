theory ProofN
imports Main
        "../Naturals"
begin

(* TEST: hipster leq lez *)
(* TEST: hipster_cond lezp leq *)

(* TEST: hipster leq lezpp eqN *)
lemma eqSym [thy_expl]: "eqN x y = eqN y x" (* requires schemes AND also to take care of arbitrary inductibles *)
by hipster_induct_schemes (*
apply(induction x rule: eqN.induct)
apply(simp_all)
done*)

lemma lemma_ae_own : "lezp x3 \<Longrightarrow> leq x3 y" by hipster_induct_simp_metis (*
apply(induction x3) (* case_tac x3 *)
apply(simp_all)
done*)

(* hipster add mul *)
(* TEST: hipster leq geq  -- works perfectly
lemma lemma_a [thy_expl]: "leq x2 x2 = True" by hipster_induct_simp_metis
lemma lemma_aa [thy_expl]: "geq x2 x2 = True" by hipster_induct_simp_metis
lemma lemma_ab [thy_expl]: "geq Z x2 = leq x2 Z" by hipster_induct_simp_metis
lemma lemma_ac [thy_expl]: "leq x2 (S x2) = True" by hipster_induct_simp_metis
lemma lemma_ad [thy_expl]: "geq x2 (S x2) = False" by hipster_induct_simp_metis
lemma lemma_ae [thy_expl]: "leq (S x2) x2 = False" by hipster_induct_simp_metis
lemma lemma_af [thy_expl]: "geq (S x2) x2 = True" by hipster_induct_simp_metis
lemma lemma_ag [thy_expl]: "leq (S Z) x2 = geq x2 (S Z)" by hipster_induct_simp_metis
lemma lemma_ah [thy_expl]: "geq (S Z) x2 = leq x2 (S Z)" by hipster_induct_simp_metis *)

lemma geq2leq [thy_expl]: "geq x y = leq y x"  (* requires arbitrary care + schemes *)
apply(induction x y rule: geq.induct)
apply(simp_all add: thy_expl)
done

(* Removed for symmetry reasons
lemma unknownLG [thy_expl]: "leq (S x) y = geq y (S x)"
by (hipster_induct_schemes (*Naturals.leq.simps Naturals.geq.simps*) (*Naturals.lemma_ab*))
(*apply(induction y rule: leq.induct)
apply(simp_all add: lemma_ab)
done*)
*)
lemma unknownLG' [thy_expl]: "geq (S x) y = leq y (S x)"
by (hipster_induct_simp_metis (*Naturals.leq.simps Naturals.geq.simps Naturals.lemma_ab*))

lemma unknownLGS [thy_expl]: "geq (S x) (S y) = leq y x"
by hipster_induct_simp_metis

(*hipster add leq*)
(*hipster add geq*)
(*hipster mul leq add*)

(* TEST: hipster_cond lez leq eqN geq *)
lemma lemma_a2 [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_aa2 [thy_expl]: "eqN x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ab2 [thy_expl]: "geq x2 x2 = True"
apply (induction x2)
apply simp_all
(*by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)*)
oops

hipster leq geq

(* TODO: uncomment, for now comment some of the def-dependent ones*)
lemma lemma_ac2 [thy_expl]: "leq x2 Z = lez x2" (* NB: used to be problematic *)
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ad2 [thy_expl]: "eqN x2 Z = lez x2"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TODO: uncomment, takes long*)
lemma lemma_ae2 [thy_expl]: "geq Z x2 = lez x2" (* NB: used to be problematic *)
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_af2 [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ag2 [thy_expl]: "eqN x2 (S x2) = False"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TODO: uncomment, they take long*)
lemma lemma_ah2 [thy_expl]: "geq x2 (S x2) = False" (* NB: used to be problematic *)
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ai [thy_expl]: "leq (S x2) x2 = False" (* NB: used to be problematic *)
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_aj [thy_expl]: "geq (S x2) x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* FIXME: another missing precond? nah, just repetition
lemma lemma_ak [thy_expl]: "leq (S Z) x2 = geq x2 (S Z)"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

(* TODO: uncomment, takes long *)
lemma lemma_al [thy_expl]: "geq (S Z) x2 = leq x2 (S Z)" (* NB: used to be problematic *)
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TEST: hipster_cond lezp leq *)
(* TODO: uncomment, takes long ?*)
lemma lemma_az [thy_expl]: "leq x2 Z = lezp x2"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps)


(* Interesting ones discovered *)
lemma lezpKer [thy_expl]: "lezp y \<and> lezp x \<Longrightarrow> x = y"
by (metis lezp.simps lezp.elims)
(* apply(case_tac y, case_tac x) >> simp_all too *) (* XXX: add elims? case_tac fallback? *)

(*hipster_cond lezpp leq*)
(* TODO: uncomment, takes long*)
lemma lemma_lezpp [thy_expl]: "lezpp x3 \<Longrightarrow> leq x3 (S y3)"
by (hipster_induct_simp_metis Naturals.lezpp.simps Naturals.leq.simps) (* NB: used to be problematic *)

(* comparison : these depend on binary leq as condition \<Longrightarrow> won't get them yet *)
lemma succKeeps : "leq m n \<Longrightarrow> leq (S m) (S n)"
by simp

(* NOTE: added to simpset, easens up next lemma ... Ensure Hipster tactics do this appropriately
    Also: should there be a "post"-first attempt rounds in case later discovered lemmas help with
      priorly non-possible ones? Does it do it already? *)
lemma succIncreasedL: "leq (S n) m \<Longrightarrow> leq n m" (* FIXME: gets stuck in a simp loop... check other lemmas *)
by hipster_induct_schemes (*
apply(induction m rule: leq.induct)
apply(simp_all)
done*)
lemma succIncreasesL : "leq m n \<Longrightarrow> leq m (S n)" by hipster_induct_schemes (*
apply(simp add: succIncreasedL)
done*)

lemma succKeepsG : "geq m n \<Longrightarrow> geq (S m) (S n)" by simp

lemma succIncreasedG: "geq n (S m) \<Longrightarrow> geq n m" (* FIXME: gets stuck in a simp loop... check other lemmas *)
by hipster_induct_schemes (*
apply(induction m rule: leq.induct)
apply(simp_all)
done*)
lemma succIncreasesG : "geq m n \<Longrightarrow> geq (S m) n" by hipster_induct_schemes (*
apply(simp add: succIncreasedG)
done*)

lemma addId: "add m Z = m" (* will go down to structural induction? *)
by hipster_induct_simp_metis (*
apply(induction m)
apply(simp_all)
done*)

lemma addIncreases: "leq n (add n m)" (* now succeeds in both *) (* oops in Hipster? *)
by hipster_induct_simp_metis (*
apply(induction n)
apply(simp_all)
done*)

lemma addIncreasesNon: "leq n (add m n)"
(*slow Hipster... doesn't prove it? *)
(* ah, with necessary one yeap *)
by (hipster_induct_simp_metis succIncreasedL) (* NOTE: will get stuck if duplicate defs are given *)
(* before:  apply(induction m)  apply(simp_all) apply(induction n)  apply(simp_all add: succIncreasedL) *)

lemma subBounded: "sub n (add n m) = Z"
by hipster_induct_simp_metis

lemma noLowerZ: "leq n Z \<Longrightarrow> n = Z" (* will fail with the rule stated *)
(* by (metis Nat.distinct(1) leq.elims(2)) *)
by hipster_induct_simp_metis (* tactic {* Tactic_Data.routine_tac @{context}*}) if lemma_az is in thy_expl*)
(*
apply(induction n)
by(simp_all) *)

(* TODO: don't we retrieve ALL existing lemmas not only thy_expl ones? it won't work without succIncreasesL ... *)
lemma subDecreases: "leq (sub n m) n" (* requires both schemes + arbitrary care *)
by (hipster_induct_schemes succIncreasesL)(*
apply(induction n m rule: sub.induct) (* TODO: add induction on several variables simultaneously: exists? does it depend on params of functions? *)
apply(simp_all add: lemma_a succIncreasesL)
done*)

lemma subHard: "leq n m \<Longrightarrow> leq (sub n m) Z"  (* seems to need the induction on both *) (* requires arbitrary care + schemes *)
by hipster_induct_schemes (*
apply(induction n m rule: leq.induct)
by (simp_all)*)

lemma subCon: "\<not> leq n m \<Longrightarrow> \<not> leq (sub n m) Z"  (* seems to need the induction on both *)  (* requires arbitrary care + schemes *)
by hipster_induct_schemes
(*apply(induction n m rule: leq.induct)
by (simp_all)*)
(* won't work: by (hipster_induct_simp_metis Naturals.sub.simps Naturals.leq.simps)*)

lemma addS2: "add n (S m) = S (add n m)"
by hipster_induct_simp_metis

lemma notLessSwap: "\<not> leq n m \<Longrightarrow> leq m n"  (* requires arbitrary care + schemes *)
by hipster_induct_schemes (*
apply(induction m rule: leq.induct)
by (simp_all)*)

lemma subId: "sub n Z = n"
(* apply(hipster_induct_schemes add.simps) *)
by hipster_induct_simp_metis



end

