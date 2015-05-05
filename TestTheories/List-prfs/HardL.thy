theory HardL
imports MediumL
        "../Nat-prfs/ProofN"

begin


fun sorted :: "Nat List \<Rightarrow> bool" where
  "sorted Nil                   = True"
| "sorted (Cons _ Nil)          = True"
| "sorted (Cons r (Cons t ts))  = (leq r t \<and> sorted (Cons t ts))"

fun insert :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if leq r t then Cons r (Cons t ts) else (Cons t (insert r ts)))"

fun isort :: "Nat List \<Rightarrow> Nat List" where
  "isort Nil = Nil"
| "isort (Cons t ts) = insert t (isort ts)"

fun qsort :: "Nat list \<Rightarrow> Nat list" where
  "qsort [] = []"
| "qsort (t # ts) = [r . r <- ts, leq r t] @ (t # [r . r <- ts, \<not> (leq r t)])"

fun sorted' :: "Nat list \<Rightarrow> bool" where
  "sorted' []                   = True"
| "sorted' [x]         = True"
| "sorted' (r # (t # ts))  = (leq r t \<and>  sorted' (t # ts))"

fun count' :: "'a \<Rightarrow> 'a List \<Rightarrow> Nat" where
  "count' n Nil = Z"
| "count' n (Cons t ts) = (if n = t then S (count' n ts) else count' n ts)"

fun elem' :: "'a \<Rightarrow> 'a List \<Rightarrow> bool" where
  "elem' n Nil = False"
| "elem' n (Cons t ts) = (n = t \<or> elem' n ts)"

lemma elemIns0: "elem t (insert t ts)"
by hipster_induct_simp_metis

lemma elemIns : "\<not> eqN r t \<Longrightarrow> elem r (insert t ts) = elem r ts"
by hipster_induct_simp_metis

lemma elemCount: "elem t ts \<Longrightarrow> lt Z (count t ts)"
by hipster_induct_simp_metis

lemma countIns: "S (count t ts) = count t (insert t ts)"
by hipster_induct_simp_metis

lemma eqEq: "eqN r t = (r = t)"
by hipster_induct_schemes

lemma countIns0: "\<not> eqN r t \<Longrightarrow> count t ts = count t (insert r ts)"
by hipster_induct_simp_metis

lemma setCountSort: "count t ts = count t (isort ts)"
by (hipster_induct_schemes eqEq countIns0 countIns)  (* XXX: something weird with regular induct: shouldn't *)

lemma subLCount : "leq (count t ts) (len ts)"
by (hipster_induct_simp_metis succIncreasesL)
(* apply(induction t ts rule: count.induct)
apply(simp_all add: succIncreasesL)*)

(*lemma count2 : "leq (add (count t ts) (count r ts)) (len ts)"
apply (hipster_induct_schemes count03 subLCount)*)


lemma symList  : "ts = rev ts \<Longrightarrow> app (rev (drop n ts)) (rev (take n ts)) = ts"
(*apply (hipster_induct_schemes dropTake)*)
oops

lemma insLen : "len (insert t ts) = S (len ts)"
by hipster_induct_simp_metis (*
apply(induction ts)
apply(simp_all)
oops*)

lemma lenIsort : "len (isort ts) = len ts"
by (hipster_induct_simp_metis insLen)


(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma appZips  : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
(*apply(hipster_induct_schemes app.simps len.simps List.exhaust Nat.distinct)*)
apply hipster_induct_schemes
by (tactic {* let 
      val lemmas = [] (* (ThyExpl_Data.proved_of_ctxt @{context}) @ (Hipster_Rules.get @{context})*)
      val facts = @{thms app.simps  len.simps List.exhaust Nat.distinct} in
        ALLGOALS(Ind_Tacs.induct_simp_or_metis (facts,lemmas) @{context} (SOME @{thms "zip.induct"}) (SOME ["a","b"]))
      end*})
(*apply(induction a b rule: zip.induct)
apply(simp_all)
by (metis app.simps len.simps List.exhaust Nat.distinct)*)


lemma auxRev : "rev (rev (Cons a Nil)) = Cons a Nil"
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma revA : "rev (app xs (Cons x Nil)) = app (rev (Cons x Nil)) (rev xs)"
by hipster_induct_simp_metis

declare [[ML_print_depth = 100]]

lemma revA' : "rev (app xs (Cons x Nil)) = Cons x (rev xs)"
by hipster_induct_simp_metis

(* FIXME: there is something wrong going on with the simplifying part: the following is resolved
    without any issues, however it won't do so with
      by (hipster_induct_schemes revA) nor by (hipster_induct_simp_metis revA) *)
lemma revRev  : "rev (rev xs) = xs"
by (hipster_induct_simp_metis revA) (*revA'*)
(*apply(induction xs)
apply(simp_all add: revA)
done*)

(*hipster rev app*)
lemma lemma_ab : "app (app x y) x = app x (app y x)"
by hipster_induct_simp_metis

lemma lemma_ad : "app (app x y) y = app x (app y y)"
by hipster_induct_simp_metis

lemma lemma_ae : "app (app x x) y = app x (app x y)"
by hipster_induct_simp_metis

lemma appAssoc : "app (app x y) z = app x (app y z)"
by hipster_induct_simp_metis

lemma appNil: "app ts Nil = ts" (* borrowed from BasicL *)
by hipster_induct_simp_metis

lemma appRevAntiDistr [thy_expl] : "app (rev x) (rev y) = rev (app y x)"
by (hipster_induct_simp_metis appNil appAssoc)

lemma revApp: "rev (app xs ts) = app (rev ts) (rev xs)"
by (hipster_induct_simp_metis appAssoc app.simps)

(* immediately follows *)
lemma s : "t = rev t \<Longrightarrow> rev (app t t) = app t t"
(*apply(hipster_induct_schemes revA appNil appAssoc)*)
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma revCons: "rev (Cons t ts) = app (rev ts) (Cons t Nil)"
by simp

(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
apply(induction rs ts rule: zip.induct)
apply(simp_all (*add: appZips*))
oops

end

