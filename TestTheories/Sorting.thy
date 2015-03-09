theory Sorting
imports Main
        Nat
        Listing
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
(*
fun merge :: "Nat list \<Rightarrow> Nat list \<Rightarrow> Nat list" where
  "merge [] ts = ts"
| "merge rs [] = rs"
| "merge (r#rs) (t#ts) = (if leq r t then (r # (merge rs (t # ts)) )
                                     else (t # (merge (r # rs) ts) ) )"

fun msort :: "Nat list \<Rightarrow> Nat list" where
  "msort [] = []"
| "msort [t] = [t]"
| "msort ts = merge (msort (take ((length ts) div 2) ts))
                    (msort (drop ((length ts) div 2) ts))*)
(* in a let ... *)

(*hipster_cond sorted insert*)

lemma insSorted: "insert r (isort ts) = isort (insert r ts)"
(* case with r = Z *)
oops
lemma insTwiceComm: "insert r (insert t ts) = insert t (insert r ts)"
(* case with r = Z *)
oops
lemma insMinInsorted: "sorted ts \<Longrightarrow> isort (insert Z ts) = insert Z ts"
oops
lemma insSomeInsorted: "sorted ts \<Longrightarrow> isort (insert t ts) = insert t ts"
oops
lemma insSortInvarZ: "sorted ts \<Longrightarrow> sorted (insert Z ts)"
by (hipster_induct_simp_metis Sorting.sorted.simps Sorting.insert.simps)
(* alternative: apply(case_tac ts) apply(simp_all) done *)
(* manual one *)
lemma leqRev: "\<not> leq r t \<Longrightarrow> leq t r"
apply(induction r rule: leq.induct)
apply(simp_all)
done
lemma insSortInvar: "sorted ts \<Longrightarrow> sorted (insert t ts)"
apply(induction ts rule: insert.induct)
apply(simp_all)
sorry
lemma insSortInvarBis: "sorted ts \<Longrightarrow> sorted (insert t ts) = True"
oops
lemma isortSorts: "sorted (isort ts)"
by (hipster_induct_simp_metis sorted.simps isort.simps insert.simps insSortInvar)
(* started as:  apply(induction ts rule: isort.induct)  apply(simp_all) apply(simp add: insSortInvar) *)
lemma isortIdsP: "sorted ts \<Longrightarrow> sorted (isort ts)"
by (hipster_induct_simp_metis sorted.simps isort.simps isortSorts)

lemma isortIds: "sorted ts \<Longrightarrow> isort ts = ts"
apply(induction ts rule: sorted.induct)
apply(simp_all)
done

lemma kerIsort: "isort (isort ts) = isort ts"
by (hipster_induct_simp_metis sorted.simps isort.simps isortSorts isortIds)
(* apply(induction ts rule: isort.induct) apply(simp_all add: isortIds) *)

lemma postOverPrecond: "sorted (insert t ts) \<Longrightarrow> sorted ts"
oops

(* qsort *)



end


