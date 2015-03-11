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

(* less or equal to Z *)
definition leZ :: "Nat => bool" where
  "leZ x = (x = Z)"

(* greater or equal to Z *)
definition geZ :: "Nat => bool" where
  "geZ _ = True"

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

definition lt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "lt a b = (leq a b \<and> \<not> leq b a)"

fun lt' :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "lt' Z (S _) = True"
| "lt' _ Z     = False"
| "lt' (S n) (S m) = lt' n m"

definition gt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "gt a b = (geq a b \<and> (\<not> geq b a))"

fun gt' :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "gt' Z _ = False"
| "gt' _ Z = True"
| "gt' (S n) (S m) = gt' n m"

fun max :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "max Z n = n"
| "max m Z = m"
| "max (S n) (S m) = S (max n m)"

(*TEST: hipster leq *) (*
lemma lemma_a [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.leq.simps)

lemma lemma_aa [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_simp_metis Naturals.leq.simps)

lemma lemma_ab [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_simp_metis Naturals.leq.simps) *)

fun lez :: "Nat \<Rightarrow> bool" where
  "lez x = (x = Z)"
(* FIXME: primes ( ' ) are not liked... bash script errors... escape properly? *)
fun lezp :: "Nat \<Rightarrow> bool" where
  "lezp Z = True"
| "lezp _ = False"
fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"
definition leZZ :: "Nat \<Rightarrow> bool" where
  "leZZ x = eqN x Z"
fun lezpp :: "Nat \<Rightarrow> bool" where
  "lezpp x = eqN x Z"

(* TEST: hipster leq lezpp eqN *)
lemma unknown1 [thy_expl]: "eqN x y = eqN y x" (* not proven by Hipster, although discovered *)
apply(induction x rule: eqN.induct)
apply(simp_all)
done
(* TEST: hipster leq leZZ *)
lemma unknown2 [thy_expl]: "leZZ (S x) = False"
by(simp add: leZZ_def)
(* TEST: hipster leq lez *)
(* hipster leq lezp *)

(* TEST: hipster_cond lezp leq *)
 (* FIXME: how on earth did this make it through?
lemma lemma_ad [thy_expl]: "leq x3 y3 = True"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps) *)
(* FIXME: how come this proof was returned? scopes wrong?
lemma lemma_ae [thy_expl]: "lezp x3 = leq x3 y3"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps) *)
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
apply(induction x rule: geq.induct)
apply(simp_all add: help01)
done
(* manual *)

lemma unknownLG [thy_expl]: "leq (S x) y = geq y (S x)"
by (hipster_induct_schemes (*Naturals.leq.simps Naturals.geq.simps*) (*Naturals.lemma_ab help01*))
(*apply(induction y rule: leq.induct)
apply(simp_all add: help01)
done*)

lemma unknownLG' [thy_expl]: "geq (S x) y = leq y (S x)"
by (hipster_induct_simp_metis Naturals.leq.simps Naturals.geq.simps (*Naturals.lemma_ab help01*))
(* oops *)

lemma unknown [thy_expl]: "geq (S x) (S y) = leq y x"
oops
(*hipster add leq*)
(*hipster add geq*)
(*hipster mul leq add
hipster_cond leZ add mul leq
hipster_cond (leq x) add mul leq
hipster_cond eqN add mul leq geq*)
(* hipster_cond leZ add leq
hipster_cond (leq x) leq leZ *)
(* hipster_cond leq geq *)
(* hipster_cond eqN add *)

(* TEST: hipster_cond lez leq eqN geq *)
lemma lemma_a2 [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_aa2 [thy_expl]: "eqN x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ab2 [thy_expl]: "geq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TODO: uncomment, for now comment some of the def-dependent ones
lemma lemma_ac2 [thy_expl]: "leq x2 Z = lez x2"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

lemma lemma_ad2 [thy_expl]: "eqN x2 Z = lez x2"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TODO: uncomment, takes long
lemma lemma_ae2 [thy_expl]: "geq Z x2 = lez x2"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

lemma lemma_af2 [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ag2 [thy_expl]: "eqN x2 (S x2) = False"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* TODO: uncomment, they take long
lemma lemma_ah2 [thy_expl]: "geq x2 (S x2) = False"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

lemma lemma_ai [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

lemma lemma_aj [thy_expl]: "geq (S x2) x2 = True"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps)

(* FIXME: another missing precond? nah, just repetition
lemma lemma_ak [thy_expl]: "leq (S Z) x2 = geq x2 (S Z)"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

(* TODO: uncomment, takes long
lemma lemma_al [thy_expl]: "geq (S Z) x2 = leq x2 (S Z)"
by (hipster_induct_simp_metis Naturals.lez.simps Naturals.leq.simps Naturals.eqN.simps Naturals.geq.simps) *)

lemma unknown [thy_expl]: "equal_Nat x y = equal_Nat y x"
oops

lemma unknown [thy_expl]: "eqN x y = equal_Nat x y"
oops

lemma unknown [thy_expl]: "eqN x y = equal_Nat y x"
oops

lemma unknown [thy_expl]: "geq x y = leq y x"
oops

lemma unknown [thy_expl]: "equal_Nat x x = True"
oops

lemma unknown [thy_expl]: "equal_Nat x Z = lez x"
oops

lemma unknown [thy_expl]: "equal_Nat Z x = lez x"
oops

lemma unknown [thy_expl]: "equal_Nat Z Z = True"
oops

lemma unknown [thy_expl]: "eqN x (S y) = equal_Nat x (S y)"
oops

lemma unknown [thy_expl]: "leq (S x) y = geq y (S x)"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) y = equal_Nat y (S x)"
oops

lemma unknown [thy_expl]: "eqN (S x) y = equal_Nat y (S x)"
oops

lemma unknown [thy_expl]: "geq (S x) y = leq y (S x)"
oops

lemma unknown [thy_expl]: "equal_Nat x (S x) = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) x = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) (S y) = equal_Nat x y"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) (S y) = equal_Nat y x"
oops

lemma unknown [thy_expl]: "eqN (S x) (S y) = equal_Nat x y"
oops

lemma unknown [thy_expl]: "eqN (S x) (S y) = equal_Nat y x"
oops

lemma unknown [thy_expl]: "geq (S x) (S y) = leq y x"
oops

lemma unknown [thy_expl]: "eqN x (S Z) = equal_Nat x (S Z)"
oops

lemma unknown [thy_expl]: "equal_Nat Z (S x) = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) Z = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) (S x) = True"
oops

lemma unknown [thy_expl]: "equal_Nat (S Z) x = equal_Nat x (S Z)"
oops

lemma unknown [thy_expl]: "eqN (S Z) x = equal_Nat x (S Z)"
oops

lemma unknown [thy_expl]: "equal_Nat (S x) (S Z) = lez x"
oops

lemma unknown [thy_expl]: "equal_Nat (S Z) (S x) = lez x"
oops

lemma unknown [thy_expl]: "equal_Nat Z (S Z) = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S Z) Z = False"
oops

lemma unknown [thy_expl]: "equal_Nat (S Z) (S Z) = True"
oops

lemma unknown [thy_expl]: "lez y \<Longrightarrow> equal_Nat x y = leq x y"
oops

lemma unknown [thy_expl]: "lez x \<Longrightarrow> equal_Nat x y = leq y x"
oops

lemma unknown [thy_expl]: "lez x \<Longrightarrow> equal_Nat x (S y) = False"
oops

lemma unknown [thy_expl]: "lez y \<Longrightarrow> equal_Nat (S x) y = False"
oops

lemma unknown [thy_expl]: "lez y \<Longrightarrow> equal_Nat (S x) (S y) = leq x y"
oops

lemma unknown [thy_expl]: "lez x \<Longrightarrow> equal_Nat (S x) (S y) = leq y x"
oops

(* for some reason, Naturals.leZ.simps appears BUT it should be Naturals.leZ_def since it is a definition...
    is it because we ourselves add it artificially to the simpset somewhere? or what is behind the appearance
    of leZ as a function with an associated simplification rule? *)
(* Uncomment: hipster_cond leZ leq *)
lemma lemma_a3 [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_simp_metis Naturals.leZ_def Naturals.leq.simps)

lemma lemma_aa3 [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_simp_metis Naturals.leZ_def Naturals.leq.simps)

(* TODO: uncomment, takes long
lemma lemma_ab3 [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_simp_metis Naturals.leZ_def Naturals.leq.simps) *)

lemma unknown [thy_expl]: "equal_Nat x y = equal_Nat y x" oops
lemma unknown [thy_expl]: "equal_Nat x x = True" oops
lemma unknown [thy_expl]: "equal_Nat x Z = leZ x" oops
lemma unknown [thy_expl]: "leq x Z = leZ x" oops
lemma unknown [thy_expl]: "equal_Nat Z x = leZ x" oops
lemma unknown [thy_expl]: "leZ Z = True" oops (* by (metis leZ_def) *)
lemma unknown [thy_expl]: "equal_Nat Z Z = True" oops
lemma unknown [thy_expl]: "equal_Nat (S x) y = equal_Nat y (S x)" oops
lemma unknown [thy_expl]: "equal_Nat x (S x) = False" oops
lemma unknown [thy_expl]: "leZ (S x) = False" oops (* by (simp add: leZ_def) *)
lemma unknown [thy_expl]: "equal_Nat (S x) x = False" oops
lemma unknown [thy_expl]: "equal_Nat (S x) (S y) = equal_Nat x y" oops
lemma unknown [thy_expl]: "equal_Nat (S x) (S y) = equal_Nat y x" oops
lemma unknown [thy_expl]: "equal_Nat Z (S x) = False" oops
lemma unknown [thy_expl]: "equal_Nat (S x) Z = False" oops
lemma unknown [thy_expl]: "equal_Nat (S x) (S x) = True" oops
lemma unknown [thy_expl]: "equal_Nat (S Z) x = equal_Nat x (S Z)" oops
lemma unknown [thy_expl]: "leZ (S Z) = False" oops (* by (simp add: leZ_def) BUT: is actually simpler than prior cases *)
lemma unknown [thy_expl]: "equal_Nat (S x) (S Z) = leZ x" oops
lemma unknown [thy_expl]: "leq (S x) (S Z) = leZ x" oops (* redundant *)
lemma unknown [thy_expl]: "equal_Nat (S Z) (S x) = leZ x" oops
lemma unknown [thy_expl]: "equal_Nat Z (S Z) = False" oops
lemma unknown [thy_expl]: "equal_Nat (S Z) Z = False" oops
lemma unknown [thy_expl]: "equal_Nat (S Z) (S Z) = True" oops
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> Z = x" oops (* again ... apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> leq x y = equal_Nat x y" oops
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq x y = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> leZ x = equal_Nat x y" oops
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> equal_Nat x (S y) = False" oops
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq x (S y) = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> equal_Nat (S x) y = False" oops
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> leq (S x) y = False" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<Longrightarrow> leq (S x) (S y) = equal_Nat x y" oops
lemma unknown [thy_expl]: "leZ x \<Longrightarrow> leq (S x) (S y) = True" oops (* apply(simp add: leZ_def) *)
lemma unknown [thy_expl]: "leZ y \<and> leZ x \<Longrightarrow> x = y"  oops (* apply(simp add: leZ_def) *)

(* TEST: hipster_cond lezp leq *)
(* TODO: uncomment, takes long ?
lemma lemma_az [thy_expl]: "leq x2 Z = lezp x2"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps) *)

(* we get some untrue statements:
    Should have: lezp x3 \<Longrightarrow> , as a condition
lemma lemma_ [thy_expl]: "leq x3 y3 = True"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps)
lemma lemma_ac [thy_expl]: "lezp x3 = leq x3 y3"
by (hipster_induct_simp_metis Naturals.lezp.simps Naturals.leq.simps) *)

(* doesn't seem to make sense it is not proven... *)
lemma unknownz [thy_expl]: "lezp y \<and> lezp x \<Longrightarrow> x = y"
apply(induction y)
apply(induction x)
apply(simp_all)
(* apply(case_tac y, case_tac x) >> simp_all too *)
done

(* FIXME: hipster_cond prints out incomplete things (sometimes conditions are missing...) *)
(* hipster_cond lezpp leq *)
(* TODO: uncomment, takes long
lemma lemma_lezpp [thy_expl]: "lezpp x3 \<Longrightarrow> leq x3 (S y3) = True"
by (hipster_induct_simp_metis Naturals.lezpp.simps Naturals.leq.simps) *)

(* comparison : these depend on binary leq as condition \<Longrightarrow> won't get them yet *)
lemma succKeeps : "leq m n \<Longrightarrow> leq (S m) (S n)"
apply(simp)
done
(* NOTE: added to simpset, easens up next lemma ... Ensure Hipster tactics do this appropriately
    Also: should there be a "post"-first attempt rounds in case later discovered lemmas help with
      priorly non-possible ones? Does it do it already? *)
lemma succIncreasedL: "leq (S n) m \<Longrightarrow> leq n m"
apply(induction m rule: leq.induct)
apply(simp_all)
done
lemma succIncreasesL : "leq m n \<Longrightarrow> leq m (S n)"
apply(simp add: succIncreasedL)
done
(*
(* cannot use \<Longleftrightarrow> ... is it because of the definitional nature of lt lifting it into meta-equality? *) 
lemma ltLt' : "lt m n = lt' m n"
apply(auto)
apply(induction m)
*)
lemma succKeepsG : "geq m n \<Longrightarrow> geq (S m) (S n)"
apply(simp)
done
lemma succIncreasedG: "geq n (S m) \<Longrightarrow> geq n m"
apply(induction m rule: leq.induct)
apply(simp_all)
done
lemma succIncreasesG : "geq m n \<Longrightarrow> geq (S m) n"
apply(simp add: succIncreasedG)
done

lemma addId: "add m Z = m"
apply(induction m)
apply(auto)
done

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
by (hipster_induct_simp_metis Naturals.sub.simps Naturals.add.simps) (* doesn't even need add.simps ... *)

lemma noLowerZ: "leq n Z \<Longrightarrow> n = Z"
apply(induction n)
apply(simp_all)
done

lemma subDecreases: "leq (sub n m) n"
apply(induction n m rule: sub.induct) (* TODO: add induction on several variables simultaneously: exists? does it depend on params of functions? *)
apply(simp_all add: lemma_a succIncreasesL)
done

lemma subHard: "leq n m \<Longrightarrow> leq (sub n m) Z "
apply(induction n m rule: leq.induct)
by (simp_all)

lemma subCon: "\<not> leq n m \<Longrightarrow> \<not> leq (sub n m) Z"
apply(induction n m rule: leq.induct)
by (simp_all)
(* won't work: by (hipster_induct_simp_metis Naturals.sub.simps Naturals.leq.simps)*)

lemma addS2: "add n (S m) = S (add n m)"
by (hipster_induct_simp_metis add.simps)

lemma notLessSwap: "\<not> leq n m \<Longrightarrow> leq m n"
(*apply(hipster_induct_schemes Naturals.leq.simps)*)
apply(induction m rule: leq.induct)
by (simp_all)

lemma subId: "sub n Z = n"
(* apply(hipster_induct_schemes add.simps) *)
by (hipster_induct_simp_metis add.simps)

end

