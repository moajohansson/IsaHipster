theory dropTake
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S Nat

fun eqN :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
  "eqN Z Z = True"
| "eqN (S n) (S m) = eqN n m"
| "eqN _     _     = False"

datatype 'a List = Nil | Cons 'a "'a List"

fun len :: "'a List \<Rightarrow> Nat" where
  "len Nil = Z"
| "len (Cons _ as) = S (len as)"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app Nil         ts = ts"
| "app (Cons r rs) ts = Cons r (app rs ts)"


fun init :: "'a List \<Rightarrow> 'a List" where
  "init Nil          = Nil"
| "init (Cons _ Nil) = Nil"
| "init (Cons t ts)  = Cons t (init ts)"

fun tail :: "'a List \<Rightarrow> 'a List" where
  "tail Nil         = Nil"
| "tail (Cons _ ts) = ts"


fun zip :: "'a List \<Rightarrow> 'b List \<Rightarrow> ('a * 'b) List" where
  "zip Nil _   = Nil"
| "zip _   Nil = Nil"
| "zip (Cons t ts) (Cons r rs) = Cons (t,r) (zip ts rs)"

(* An example for conditionals and simultaneous induction derived from _zip_'s definition:
    immediately provable by our tactic without a need for exploration *)
lemma appZips : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
  (* apply hipster_induct *)
  apply (induct a b arbitrary: c d rule: dropTake.zip.induct)
  apply simp
  apply (metis Nat.distinct(1) app.simps(1) len.elims)
  apply simp
  apply simp
  done
(*by (hipster_induct_schemes app.simps zip.simps len.simps List.exhaust Nat.distinct)*)

fun take :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "take Z     _           = Nil"
| "take _     Nil         = Nil"
| "take (S n) (Cons t ts) = Cons t (take n ts)"

fun drop :: "Nat \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "drop Z     ts          = ts"
| "drop _     Nil         = Nil"
| "drop (S n) (Cons t ts) = drop n ts"
lemma dropTake : "ts = app (take n ts) (drop n ts)"
  (* apply hipster_induct *)
  apply (induct n ts rule: dropTake.take.induct)
  apply simp
  apply simp
  apply simp
  done
  (* by hipster_induct_schemes *)
ML{* 
fun SOLVE_OR_FAIL tac st =
  let fun solved st = has_fewer_prems 1 st;
  in Seq.filter solved (tac st) end;

fun mytac ctxt = (SOLVE_OR_FAIL (Rec_Ind_Tacs.recinduct_simp ctxt)) ORELSE (Rec_Ind_Lemma_Spec_Tacs.koen_induct ctxt)
*}
method_setup recind_lemma = {*
  Scan.lift (Scan.succeed 
    (fn ctxt => SIMPLE_METHOD 
      (mytac ctxt)))
   *}


(* Similarly for the more complex in expression yet not conditional similar proposition to the above *)
lemma zipApp : "zip (app xs ys) zs = app (zip xs (take (len xs) zs)) (zip ys (drop (len xs) zs))"
  apply recind_lemma
  (* apply hipster_induct *) (* fails*)
(* by (hipster_induct_schemes app.simps zip.simps drop.simps take.simps len.simps Nat.exhaust List.exhaust) *)
  oops







fun sub :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
  "sub Z _     = Z"
| "sub (S n) Z = S n"
| "sub (S n) (S m) = sub n m"

lemma initAsTake: "init ts = take (sub (len ts) (S Z)) ts"
(*  apply hipster_induct *)
  apply (induct ts rule: dropTake.init.induct)
  apply simp
  apply simp
  apply simp
  apply (metis Nat.distinct(1) sub.elims)
  done
(* by (hipster_induct_schemes sub.simps Nat.exhaust) *)


fun count :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat" where
  "count _ Nil = Z"
| "count n (Cons t ts) = (if eqN n t then S (count n ts) else count n ts)"

lemma count01: "\<not> (eqN r t) \<Longrightarrow> count r (app ts (Cons t Nil)) = count r ts"
 (*  apply hipster_induct *) 
  apply (induct ts arbitrary: r t)
  apply simp
  apply simp
  done
(* by (hipster_induct_simp_metis) *)

lemma initTail : "init (tail x) = tail (init x)"
 (* apply hipster_induct *)
  apply (induct x)
  apply simp
  apply simp
  apply (smt List.distinct(1) init.elims tail.simps(1) tail.simps(2))
  done
(* by (hipster_induct_schemes) *)

lemma lenInitTail: "len (init x) = len (tail x)"
(*   apply hipster_induct *)
  apply (induct x)
apply simp
apply simp
  apply (metis init.simps(2) init.simps(3) len.elims len.simps(2) tail.simps(2))
  done
(* by (hipster_induct_schemes) *)


fun notNil :: "'a List \<Rightarrow> bool" where
  "notNil Nil = False"
| "notNil _   = True"

lemma initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
 (*  apply hipster_induct *)
  apply (induct rs arbitrary: ts)
  apply simp
  apply simp
  apply (metis app.elims init.simps(3) notNil.elims(2))
  done
(* by (hipster_induct_schemes notNil.elims init.simps app.simps) *)

end

