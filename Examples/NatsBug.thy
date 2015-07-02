theory NatsBug
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S Nat

fun leq :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "leq Z _ = True"
| "leq _ Z = False"
| "leq (S x) (S y) = leq x y"

fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where (* own definition for equality *)
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"

(* less or equal to Z *)
fun lez :: "Nat \<Rightarrow> bool" where          (* - as a function definition relying on Isabelle's equality *)
  "lez x = (x = Z)"

fun lezP :: "Nat \<Rightarrow> bool" where         (* - as a function definition via pattern matching *)
  "lezP Z = True"
| "lezP _ = False"

fun lezzP :: "Nat \<Rightarrow> bool" where        (* - as a function definition via our own equality *)
  "lezzP x = eqN x Z"

definition leZ :: "Nat \<Rightarrow> bool" where   (* - as a constant definition relying on Isabelle's equality *)
  "leZ x \<equiv> (x = Z)"

definition leZZ :: "Nat \<Rightarrow> bool" where  (* - as a constant definition relying on own equality *)
  "leZZ x \<equiv> eqN x Z"


(* hipster_cond lezzP leq *) (* skipping of conditions in output solved *)
(* hipster_cond lezP leq *)  (* skipping of conditions in output solved *)

(* hipster lezzP *) (* nothing weird, ok *)
(* hipster lezP *)  (* everything trivial, ok*)


(* FIXME: 1. Isabelle's equality = (gets translated as a separate predicate Haskell
             function equal_<Type> which will be missing in the original theory) *)
(* hipster lez *)  (* equations only with lez are trivial, aren't returned *)
lemma unknown [thy_expl]: "equal_Nat x y = equal_Nat y x" (* free variable equal_Nat instead of equality = *)
oops


(** QUICK REFERENCE: Haskell transaltions **)
(*  equal_Nat :: Nat -> Nat -> Bool
    equal_Nat Z (S nat) = False
    equal_Nat (S nat) Z = False
    equal_Nat (S nata) (S nat) = equal_Nat nata nat
    equal_Nat Z Z = True
    
    leZ :: Nat -> Bool
    leZ x = equal_Nat x Z
    
    lez :: Nat -> Bool
    lez x = equal_Nat x Z *)

(*  eqN :: Nat -> Nat -> Bool
    eqN Z Z = True
    eqN (S n) (S m) = eqN n m
    eqN (S v) Z = False
    eqN Z (S v) = False
    
    leZZ :: Nat -> Bool
    leZZ x = eqN x Z
    
    lezzP :: Nat -> Bool
    lezzP x = eqN x Z
    
    lezP :: Nat -> Bool
    lezP Z = True
    lezP (S v) = False *)

(*  leq :: Nat -> Nat -> Bool
    leq Z uu = True
    leq (S v) Z = False
    leq (S x) (S y) = leq x y *)


(*  Notes to self  *)
(* cond with: lezP leq*)
lemma dub00 [thy_expl]: "lezP y \<and> lezP x \<Longrightarrow> x = y" (* Hipster fails for some reason: no double induction? *)
apply(induction y, induction x)
by (simp_all)

(* Constant definition issues *)
(* leZ *)
lemma dub01 [thy_expl]: "leZ (S Z) = False" (* Hipster fails *)
(* Hipster does not get leZ_def, but it also fails when provided manually with it:
    by (hipster_induct_simp_metis NatsBug.leZ_def) *)
by (simp add: leZ_def)

(* leZZ *)
lemma dub02 [thy_expl]: "eqN Z x = leZZ x" (* Hipster fails *)
apply (induction x)
by (simp_all add: leZZ_def)


end

