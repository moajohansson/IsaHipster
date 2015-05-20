theory Sorted
imports Main
        "../Sorting"
        HardL

begin


lemma leqRev [] : "\<not> leq r t \<Longrightarrow> leq t r" (* without other lemmas, requires schemes *)
by hipster_induct_schemes (*
apply(induction r rule: leq.induct)
apply(simp_all)
done*)

lemma leqLeqEq : "\<lbrakk> leq r t ; leq t r \<rbrakk> \<Longrightarrow> r = t"
by (hipster_induct_schemes) (* without other lemmas, requires schemes *)

lemma insSorted : "insert r (isort ts) = isort (insert r ts)"
apply(induction ts rule: isort.induct)
apply(simp_all add: leqRev leqLeqEq)
(* case with r = Z *)
oops

lemma insTwiceComm : "insert r (insert t ts) = insert t (insert r ts)"
(* case with r = Z *)
oops

lemma isortIds : "sorted ts \<Longrightarrow> isort ts = ts"
by hipster_induct_schemes (*
apply(induction ts rule: sorted.induct)
apply(simp_all)
done*)

lemma insSortInvarZ : "sorted ts \<Longrightarrow> sorted (insert Z ts)"
by (hipster_induct_simp_metis)
(* alternative: apply(case_tac ts) apply(simp_all) done *)

lemma insSortInvar : "sorted ts \<Longrightarrow> sorted (insert t ts)"(*
by (hipster_induct_schemes sorted.simps leqRev)*)
apply(induction ts rule: sorted.induct)
apply(simp_all)
apply(metis sorted.simps insert.simps leqRev)
sledgehammer
by (metis (full_types) leqRev)

lemma isortSorts : "sorted (isort ts)"
by (hipster_induct_simp_metis insSortInvar)
(* started as:  apply(induction ts rule: isort.induct)  apply(simp_all) apply(simp add: insSortInvar) *)

lemma isortIdsP : "sorted ts \<Longrightarrow> sorted (isort ts)"
by (hipster_induct_simp_metis isortSorts)

lemma kerIsort : "isort (isort ts) = isort ts"
by (hipster_induct_simp_metis isortSorts isortIds)
(* apply(induction ts rule: isort.induct) apply(simp_all add: isortIds) *)

lemma insMinInsorted : "sorted ts \<Longrightarrow> isort (insert Z ts) = insert Z ts"
by (hipster_induct_simp_metis isortIds insSortInvar)

lemma insSomeInsorted : "sorted ts \<Longrightarrow> isort (insert t ts) = insert t ts"
by (hipster_induct_simp_metis isortIds insSortInvar)


lemma postOverPrecond: "sorted (insert t ts) \<Longrightarrow> sorted ts"
apply(induction t ts rule: insert.induct)
apply(simp_all add: leqRev leqLeqEq)
oops


end
