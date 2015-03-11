theory Naturals
imports Main
        "../IsaHipster"
begin

datatype Nat = Z | S Nat

fun leq :: "Nat => Nat => bool" where
  "leq Z _ = True"
| "leq _ Z = False"
| "leq (S x) (S y) = leq x y"

fun geq :: "Nat => Nat => bool" where
  "geq _ Z = True"
| "geq Z _ = False"
| "geq (S x) (S y) = geq x y"

fun add :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "add Z     n = n"
| "add (S n) m = S (add n m)"

fun sub :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "sub Z _     = Z"
| "sub (S n) Z = S n"
| "sub (S n) (S m) = sub n m"

(* we do all tail-recursion + call recursing on 1ast argument but
    should not be a need (?) *)
fun mul :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "mul Z     _ = Z"
| "mul (S n) m = add m (mul n m)"

fun exp :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "exp Z     _ = S Z"
| "exp (S n) m = mul m (exp n m)"

fun lt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "lt Z (S _) = True"
| "lt _ Z     = False"
| "lt (S n) (S m) = lt n m"

fun gt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "gt Z _ = False"
| "gt _ Z = True"
| "gt (S n) (S m) = gt n m"

fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"

fun max :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "max Z n = n"
| "max m Z = m"
| "max (S n) (S m) = S (max n m)"

fun lez :: "Nat \<Rightarrow> bool" where
  "lez x = (x = Z)"
(* FIXME: primes ( ' ) are not liked... bash script errors... escape properly? *)
fun lezp :: "Nat \<Rightarrow> bool" where
  "lezp Z = True"
| "lezp _ = False"
fun lezpp :: "Nat \<Rightarrow> bool" where
  "lezpp x = eqN x Z"

(* TEST: hipster leq lezpp eqN *)
lemma unknown1 [thy_expl]: "eqN x y = eqN y x" (* not proven by Hipster, although discovered *)
by (hipster_induct_schemes)(*
apply(induction x rule: eqN.induct)
apply(simp_all)
done*)

(* TEST: hipster leq lez *)
(* hipster leq lezp *)

(* TEST: hipster_cond lezp leq *)
lemma lemma_ae_own : "lezp x3 \<Longrightarrow> leq x3 y"
apply(induction x3) (* case_tac x3 *)
apply(simp_all)
done
(* Interesting ones discovered *)
lemma unknown [thy_expl]: "lezp y \<and> lezp x \<Longrightarrow> x = y" oops

(* hipster add mul *)
(* TEST: hipster leq geq *)
lemma lemma_a [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_aa [thy_expl]: "geq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ab [thy_expl]: "geq Z x2 = leq x2 Z"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ac [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ad [thy_expl]: "geq x2 (S x2) = False"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ae [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_af [thy_expl]: "geq (S x2) x2 = True"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ag [thy_expl]: "leq (S Z) x2 = geq x2 (S Z)"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

lemma lemma_ah [thy_expl]: "geq (S Z) x2 = leq x2 (S Z)"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps)

(* manual, but: lemma_ab is the same :/ *)
lemma help01 : "geq Z n = leq n Z"
apply(case_tac n)
apply(simp_all)
done
lemma unknown [thy_expl]: "geq x y = leq y x"
(*by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps Naturals.lemma_ab)*)
by (hipster_induct_schemes Naturals.leq.simps Naturals.geq.simps)(*
apply(induction x rule: geq.induct)
apply(simp_all add: help01)
done*)
(* manual *)
(*
lemma unknownLG [thy_expl]: "leq (S x) y = geq y (S x)"
by (hipster_induct_schemes (*Naturals.leq.simps Naturals.geq.simps*) (*Naturals.lemma_ab help01*))
(*apply(induction y rule: leq.induct)
apply(simp_all add: help01)
done*)
*)
lemma unknownLG' [thy_expl]: "geq (S x) y = leq y (S x)"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps (*Naturals.lemma_ab help01*))
(* oops *)

lemma unknownLGS [thy_expl]: "geq (S x) (S y) = leq y x"
by (hipster_induct_schemes) (*oops*)

(*hipster add leq*)
(*hipster add geq*)
(*hipster mul leq add
hipster_cond (leq x) add mul leq
hipster_cond eqN add mul leq geq*)
(* hipster_cond leq geq *)
(* hipster_cond eqN add *)

(* TEST: hipster_cond lez leq eqN geq *)
lemma lemma_a2 [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_aa2 [thy_expl]: "eqN x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ab2 [thy_expl]: "geq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

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

lemma unknown [thy_expl]: "geq x y = leq y x" oops
lemma unknown [thy_expl]: "leq (S x) y = geq y (S x)" oops
lemma unknown [thy_expl]: "geq (S x) y = leq y (S x)" oops
lemma unknown [thy_expl]: "geq (S x) (S y) = leq y x" oops

(* TEST: hipster_cond lezp leq *)
(* TODO: uncomment, takes long ?*)
lemma lemma_az [thy_expl]: "leq x2 Z = lezp x2"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps)


(* doesn't seem to make sense it is not proven... *)
lemma unknownz [thy_expl]: "lezp y \<and> lezp x \<Longrightarrow> x = y" (* XXX: will work if we allow more than 1 induction (cfr: TRY...) *)
apply(induction y)
apply(induction x)
apply(simp_all)
(* apply(case_tac y, case_tac x) >> simp_all too *)
done

(* hipster_cond lezpp leq *)
(* TODO: uncomment, takes long*)
lemma lemma_lezpp [thy_expl]: "lezpp x3 \<Longrightarrow> leq x3 (S y3) = True"
by (hipster_induct_simp_metis Naturals.lezpp.simps Naturals.leq.simps) (* NB: used to be problematic *)

(* comparison : these depend on binary leq as condition \<Longrightarrow> won't get them yet *)
lemma succKeeps : "leq m n \<Longrightarrow> leq (S m) (S n)"
apply(simp)
done
(* NOTE: added to simpset, easens up next lemma ... Ensure Hipster tactics do this appropriately
    Also: should there be a "post"-first attempt rounds in case later discovered lemmas help with
      priorly non-possible ones? Does it do it already? *)
lemma succIncreasedL: "leq (S n) m \<Longrightarrow> leq n m" (* FIXME: gets stuck in a simp loop... check other lemmas *)
apply(induction m rule: leq.induct)
apply(simp_all)
done
lemma succIncreasesL : "leq m n \<Longrightarrow> leq m (S n)"
apply(simp add: succIncreasedL)
done

lemma succKeepsG : "geq m n \<Longrightarrow> geq (S m) (S n)" by simp

lemma succIncreasedG: "geq n (S m) \<Longrightarrow> geq n m" (* FIXME: gets stuck in a simp loop... check other lemmas *)
apply(induction m rule: leq.induct)
apply(simp_all)
done
lemma succIncreasesG : "geq m n \<Longrightarrow> geq (S m) n"
apply(simp add: succIncreasedG)
done

lemma addId: "add m Z = m"
by (hipster_induct_schemes Naturals.add.simps)(*
apply(induction m)
apply(auto)
done*)

lemma addIncreases: "leq n (add n m)"
(* oops in Hipster? *)
apply(induction n)
apply(simp_all)
done
lemma addIncreasesNon: "leq n (add m n)"
(*slow Hipster... doesn't prove it? *)
(* ah, with necessary one yeap *)
by (hipster_induct_simp_metis Naturals.leq.simps succIncreasedL) (* NOTE: will get stuck if duplicate defs are given *)
(* before:  apply(induction m)  apply(simp_all) apply(induction n)  apply(simp_all add: succIncreasedL) *)

lemma subBounded: "sub n (add n m) = Z"
by (hipster_induct_schemes Naturals.sub.simps Naturals.add.simps) (* doesn't even need add.simps ... *)

lemma noLowerZ: "leq n Z \<Longrightarrow> n = Z"
apply(induction n)
apply(simp_all)
done

(* TODO: don't we retrieve ALL existing lemmas not only thy_expl ones? it won't work without succIncreasesL ... *)
lemma subDecreases: "leq (sub n m) n"
by (hipster_induct_schemes Naturals.leq.simps Naturals.sub.simps succIncreasesL)(*
apply(induction n m rule: sub.induct) (* TODO: add induction on several variables simultaneously: exists? does it depend on params of functions? *)
apply(simp_all add: lemma_a succIncreasesL)
done*)

lemma subHard: "leq n m \<Longrightarrow> leq (sub n m) Z"
by (hipster_induct_schemes Naturals.leq.simps Naturals.sub.simps)(*
apply(induction n m rule: leq.induct)
by (simp_all)*)

lemma subCon: "\<not> leq n m \<Longrightarrow> \<not> leq (sub n m) Z"
by (hipster_induct_schemes Naturals.leq.simps Naturals.sub.simps)
(*apply(induction n m rule: leq.induct)
by (simp_all)*)
(* won't work: by (hipster_induct_simp_metis Naturals.sub.simps Naturals.leq.simps)*)

lemma addS2: "add n (S m) = S (add n m)"
by (hipster_induct_simp_metis add.simps)

lemma notLessSwap: "\<not> leq n m \<Longrightarrow> leq m n"
apply(hipster_induct_schemes Naturals.leq.simps)
done(*
apply(induction m rule: leq.induct)
by (simp_all)*)


lemma subId: "sub n Z = n"
(* apply(hipster_induct_schemes add.simps) *)
by (hipster_induct_simp_metis add.simps)

end

