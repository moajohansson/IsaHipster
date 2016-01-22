theory SortM
imports Main
        Naturals
        Listing
begin

fun sorted :: "nat List \<Rightarrow> bool" where
  "sorted Nil                   = True"
| "sorted (Cons _ Nil)          = True"
| "sorted (Cons r (Cons t ts))  = ( r \<le> t \<and> sorted (Cons t ts))"

fun insert :: "Nat \<Rightarrow> Nat List \<Rightarrow> Nat List" where
  "insert r Nil         = Cons r Nil"
| "insert r (Cons t ts) = (if leq r t then Cons r (Cons t ts) else (Cons t (insert r ts)))"


fun isort :: "Nat List \<Rightarrow> Nat List" where
  "isort Nil = Nil"
| "isort (Cons t ts) = insert t (isort ts)"

fun qsort :: "Nat list \<Rightarrow> Nat list" where
  "qsort [] = []"
| "qsort (t # ts) = (qsort [r <- ts. leq r t]) @ [t] @ (qsort [r <- ts. \<not> (leq r t)])"

thm qsort.induct

fun sorted2 :: "Nat list \<Rightarrow> bool" where
  "sorted2 []                   = True"
| "sorted2 [x]         = True"
| "sorted2 (r # (t # ts))  = (leq r t \<and> sorted2 (t # ts))"

fun merge :: "Nat list \<Rightarrow> Nat list \<Rightarrow> Nat list" where
  "merge rs [] = rs"
| "merge [] ts = ts"
| "merge (r#rs) (t#ts) = (if leq r t then r # merge rs (t#ts)
                                     else t # merge (r#rs) ts)"

fun msort :: "Nat list => Nat list" where
  "msort [] = []"
| "msort [t] = [t]"
| "msort ts = merge (msort (List.take (length ts div 2) ts)) (* size instead? *)
                    (msort (List.drop (length ts div 2) ts))"


lemma lemma_a [thy_expl]: "leq x2 x2 = True"
by (hipster_induct_schemes leq.simps)

lemma lemma_aa [thy_expl]: "leq x2 (S x2) = True"
by (hipster_induct_schemes leq.simps)

lemma lemma_ab [thy_expl]: "leq (S x2) x2 = False"
by (hipster_induct_schemes leq.simps)

(*hipster_cond le*)
lemma lemma_ac [thy_expl]: "leq x2 y2 \<Longrightarrow> leq x2 (S y2) = True"
by (hipster_induct_schemes leq.simps)

lemma lemma_ad [thy_expl]: "leq y2 x2 \<Longrightarrow> leq (S x2) y2 = False"
by (hipster_induct_schemes leq.simps)

lemma lemma_ae [thy_expl]: "leq y x \<and> leq x y \<Longrightarrow> x = y"
by (hipster_induct_schemes leq.simps Nat.exhaust)


lemma le_trans [thy_expl]: "leq z y \<and> leq x z \<Longrightarrow> leq x y = True"
by (hipster_induct_schemes leq.simps Nat.exhaust)

(*hipster_cond leq sorted2 merge leq

hipster_cond sorted2 leq merge sorted2


hipster merge sorted2
*)

(* lemma sortCons: "r \<le> t \<and> sorted2 (t # ts) \<Longrightarrow> sorted2 (r # (t # ts))" by simp *)
lemma insSortInvar : "sorted ts \<Longrightarrow> sorted (insert t ts)"
by hipster_induct_schemes

lemma mer1[thy_expl]: "sorted2 ts \<Longrightarrow> sorted2 (merge [] ts)"
(*by(metis sorted2.cases merge.simps)*) (* replace of cases by inductions *)
by hipster_induct_simp_metis

lemma mer2[thy_expl]: "sorted2 ts \<Longrightarrow> sorted2 (merge [t] ts)" (* sorted2.induct! *)
by hipster_induct_schemes

lemma mer3[thy_expl]: "sorted2 ts \<Longrightarrow> sorted2 (merge ts [t])" (* sorted2.induct! *)
by hipster_induct_schemes

lemma mer4[thy_expl]: "sorted2 (t # ts) \<and> \<not> (leq t r) \<Longrightarrow> sorted2 (r # (merge (t#ts) []))" by simp

lemma mer4'[thy_expl]: "sorted2 (t # ts) \<and> leq t r \<Longrightarrow> sorted2 (t # merge ts [r])"
by (hipster_induct_schemes merge.simps mer3)

lemma mer5'[thy_expl]: "sorted2 (t # ts) \<and> leq r v \<and> \<not> (leq t r) \<Longrightarrow> sorted2 (r # (merge (t#ts) [v]))"
(*apply(induction ts rule: sorted2.induct)
apply(simp_all add: mer4 mer3 mer2 mer1)
apply(metis sorted2.simps merge.simps)*)
by (hipster_induct_schemes merge.simps mer3)

lemma mer5''[thy_expl]: "sorted2 (r # rs) \<and> \<not> (leq t r) \<Longrightarrow> sorted2 (r # (merge [t] rs))"
by (hipster_induct_schemes sorted2.simps)

lemma ssu[thy_expl]: "sorted2 (r # rs) \<and> (leq t r) \<Longrightarrow> sorted2 (t # (merge [] (r#rs)))" by (metis merge.simps sorted2.simps)
(*by (hipster_induct_simp_metis)*)

lemma ssu'[thy_expl]: "sorted2 (r # rs) \<and> (leq t v) \<and> (leq t r) \<Longrightarrow> sorted2 (t # (merge [v] (r#rs)))"
by (metis mer5'' merge.simps sorted2.simps)
lemma ssu''[thy_expl]: " sorted2 [t, v] \<and> sorted2 (r # rs) \<and> leq t r \<Longrightarrow> sorted2 (t # (merge [v] (r#rs)))"
(*by (metis sorted2.simps(3) ssu')*)
by (hipster_induct_schemes sorted2.simps mer5'')

lemma cons1[thy_expl]: "sorted2 (t # ts) \<Longrightarrow> sorted2 ts"
by hipster_induct_simp_metis
(*by (metis sorted2.elims(3) sorted2.simps(3))*)

lemma t1 : "sorted2 ts \<and> ts \<noteq> [] \<and> leq t (hd ts) \<Longrightarrow> sorted2 (t # ts)"
by hipster_induct_simp_metis
(*by (metis list.sel sorted2.elims(3))*)

lemma mer6[thy_expl]: "(sorted2 ts \<and> ts \<noteq> [] \<and> sorted2 (r # rs)) \<Longrightarrow> (sorted2 ((merge ts (r#rs))))"
apply(induction ts rule: sorted2.induct)
apply(induction rs rule: sorted2.induct)
apply(simp_all only: thy_expl)
apply(simp add: ssu'')
apply(rule conjI)
apply(rule impI)
apply(simp add: thy_expl)
apply(rule impI)
apply(rule conjI)
apply(simp add: thy_expl)
apply(simp add: thy_expl)
oops
(*by (hipster_induct_schemes ssu' ssu'' mer5' mer5'' mer3)
sledgehammer
apply(metis sorted2.simps ssu'' mer3 ssu ssu' mer4 mer2 mer1 t1 mer5' mer5'' mer4')*)

(* simplification can very much screw up the goal state! *)
lemma mer5[thy_expl]: "(sorted2 (t # ts) \<and> sorted2 (r # rs) \<and> leq t r) \<Longrightarrow> (sorted2 (t # (merge ts (r#rs))))"
apply(induction ts rule: sorted2.induct)
apply(simp)
apply(simp add: mer5'')
apply(simp add: mer4' mer5'' mer3 ssu' ssu'' ssu)
apply(rule conjI)
apply(rule impI)
apply simp
apply(rule impI, rule conjI)
apply(simp_all)
apply(drule conjE)
apply(simp_all add: ssu' mer5'' mer4 mer4' mer3 mer2 mer1 ssu'' mer5')
(*apply (metis (full_types) sorted2.simps merge.simps if_splits list.exhaust list.distinct)*)
(*apply(simp add: ssu ssu' mer3 mer2 mer1 ssu'' mer5' mer4')*)
(*apply(metis merge.simps(3) mer5' mer4' mer3 mer4)*)
sorry

lemma mergeS: "sorted2 ts \<and> sorted2 rs \<Longrightarrow> sorted2 (merge ts rs)"
apply(induction ts rs rule: merge.induct)
sledgehammer
apply (metis merge.simps(1))
sledgehammer
apply (metis merge.simps(2))
sledgehammer
sledgehammer min [e] (cons1 mer4 mer5 merge.elims merge.simps(1) merge.simps(3) Nat_induct ord.lexordp_eq.simps ord.lexordp_eq_simps(3) qsort.cases sorted2.simps(3))
apply(simp_all add: mer1 mer2)
(*sledgehammer*)
by (metis mer4 mer5 merge.simps sorted2.simps)
(*
apply(cases rs)
apply(simp_all)
by (hipster_induct_schemes mer1 mer5'' mer5 merge.simps sorted2.simps)*)
(*apply(induction ts rule: sorted2.induct)
apply(simp add: mer1)
apply(simp add: mer5'')
by (metis mer4 mer5 merge.simps sorted2.simps)*)
(* apply(induction ts rule: sorted2.induct)
apply(simp add: mer1)
apply(simp add: mer2)
apply(cases rs)
apply(simp_all)
by (metis mer4 mer5 merge.simps sorted2.simps)*)
(*   by (induct xs ys rule: merge.induct) (auto simp add: ball_Un not_le less_le sorted_Cons) *)

lemma smsort: "sorted2 (msort xs)"
by (hipster_induct_schemes mergeS)

(*lemma merComm: "sorted2 ts \<and> sorted2 rs \<Longrightarrow> merge rs ts = merge ts rs"
apply(induction rs ts rule: merge.induct)
apply(simp_all)
apply(metis sorted2.cases merge.simps(1) merge.simps(2))*)



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


