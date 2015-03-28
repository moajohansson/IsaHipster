theory Sorting
imports Main
        Naturals
        Listing
begin

fun sorted :: "nat List \<Rightarrow> bool" where
  "sorted Nil                   = True"
| "sorted (Cons _ Nil)          = True"
| "sorted (Cons r (Cons t ts))  = ( r \<le> t \<and> sorted (Cons t ts))"

fun insert :: "nat \<Rightarrow> nat List \<Rightarrow> nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if r \<le> t then Cons r (Cons t ts) else (Cons t (insert r ts)))"


fun isort :: "nat List \<Rightarrow> nat List" where
  "isort Nil = Nil"
| "isort (Cons t ts) = insert t (isort ts)"

fun qsort :: "nat list \<Rightarrow> nat list" where
  "qsort [] = []"
| "qsort (t # ts) = (qsort [r <- ts. r \<le> t]) @ [t] @ (qsort [r <- ts. \<not> (r \<le> t)])"


fun sorted' :: "nat list \<Rightarrow> bool" where
  "sorted' []                   = True"
| "sorted' [x]         = True"
| "sorted' (r # (t # ts))  = (r \<le> t \<and> sorted' (t # ts))"

fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "merge rs [] = rs"
| "merge [] ts = ts"
| "merge (r#rs) (t#ts) = (if r \<le> t then r # merge rs (t#ts)
                                       else t # merge (r#rs) ts)"

fun msort :: "nat list => nat list" where
  "msort [] = []"
| "msort [t] = [t]"
| "msort ts = merge (msort (List.take (length ts div 2) ts)) (* size instead? *)
                    (msort (List.drop (length ts div 2) ts))"

(* lemma sortCons: "r \<le> t \<and> sorted' (t # ts) \<Longrightarrow> sorted' (r # (t # ts))" by simp *)

lemma mer1: "sorted' ts \<Longrightarrow> sorted' (merge [] ts)"
(*by(metis sorted'.cases merge.simps)*) (* replace of cases by inductions *)
by hipster_induct_simp_metis

lemma mer2: "sorted' ts \<Longrightarrow> sorted' (merge [t] ts)" (* sorted'.induct! *)
by hipster_induct_schemes

lemma mer3: "sorted' ts \<Longrightarrow> sorted' (merge ts [t])" (* sorted'.induct! *)
by hipster_induct_schemes

lemma mer4: "sorted' (t # ts) \<and> \<not> t \<le> r \<Longrightarrow> sorted' (r # (merge (t#ts) []))" by simp

lemma mer4': "sorted' (t # ts) \<and> t \<le> r \<Longrightarrow> sorted' (t # merge ts [r])"
by (hipster_induct_schemes merge.simps mer3)

lemma mer5': "sorted' (t # ts) \<and> r \<le> v \<and> \<not> t \<le> r \<Longrightarrow> sorted' (r # (merge (t#ts) [v]))"
(*apply(induction ts rule: sorted'.induct)
apply(simp_all add: mer4 mer3 mer2 mer1)
apply(metis sorted'.simps merge.simps)*)
by (hipster_induct_schemes merge.simps mer3)

lemma mer5'': "sorted' (r # rs) \<and> \<not> t \<le> r \<Longrightarrow> sorted' (r # (merge [t] rs))"
by (hipster_induct_schemes sorted'.simps)

lemma ssu: "sorted' (r # rs) \<and> t \<le> r \<Longrightarrow> sorted' (t # (merge [] (r#rs)))" by (metis merge.simps sorted'.simps)
(*by (hipster_induct_simp_metis)*)

lemma ssu': "sorted' (r # rs) \<and> t \<le> v \<and> t \<le> r \<Longrightarrow> sorted' (t # (merge [v] (r#rs)))"
by (metis mer5'' merge.simps sorted'.simps)

(* simplification can very much screw up the goal state! *)
lemma mer5: "(sorted' (t # ts) \<and> sorted' (r # rs) \<and> t \<le> r) \<Longrightarrow> (sorted' (t # (merge ts (r#rs))))"
apply(induction ts rule: sorted'.induct)
apply(simp)
apply(simp add: mer5'')
apply(simp add: ssu ssu' mer5' mer4') (*
apply(metis merge.simps(3) mer5' mer4' mer3 mer4)*)
sorry

lemma cons1: "sorted' (t # ts) \<Longrightarrow> sorted' ts"
by hipster_induct_simp_metis
(*by (metis sorted'.elims(3) sorted'.simps(3))*)

lemma mergeS: "sorted' ts \<and> sorted' rs \<Longrightarrow> sorted' (merge ts rs)"
apply(induction ts rs rule: merge.induct)
apply(simp_all add: mer1 mer2)
by (metis mer4 mer5 merge.simps sorted'.simps)
(*
apply(cases rs)
apply(simp_all)
by (hipster_induct_schemes mer1 mer5'' mer5 merge.simps sorted'.simps)*)
(*apply(induction ts rule: sorted'.induct)
apply(simp add: mer1)
apply(simp add: mer5'')
by (metis mer4 mer5 merge.simps sorted'.simps)*)
(* apply(induction ts rule: sorted'.induct)
apply(simp add: mer1)
apply(simp add: mer2)
apply(cases rs)
apply(simp_all)
by (metis mer4 mer5 merge.simps sorted'.simps)*)
(*   by (induct xs ys rule: merge.induct) (auto simp add: ball_Un not_le less_le sorted_Cons) *)

lemma smsort: "sorted' (msort xs)"
by (hipster_induct_schemes mergeS)

(*lemma merComm: "sorted' ts \<and> sorted' rs \<Longrightarrow> merge rs ts = merge ts rs"
apply(induction rs ts rule: merge.induct)
apply(simp_all)
apply(metis sorted'.cases merge.simps(1) merge.simps(2))*)



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



(* qsort *)



end


