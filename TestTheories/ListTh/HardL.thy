theory HardL
imports MediumL
        "../Sorting"

begin

lemma setCountSort: "count t ts = count t (isort ts)"
oops

lemma elemIns: "\<not> eqN r t \<Longrightarrow> elem r (insert t ts) = elem r ts"
by hipster_induct_simp_metis

lemma insLen: "len (insert t ts) = S (len ts)"
by hipster_induct_simp_metis (*
apply(induction ts)
apply(simp_all)
oops*)

lemma lenIsort: "len (isort ts) = len ts"
by (hipster_induct_simp_metis insLen)


(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma appZips: "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
apply(induction a b rule: zip.induct)
apply(simp_all)
apply(drule len0)
by (simp_all)

lemma auxRev: "rev (rev (Cons a Nil)) = Cons a Nil"
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma revA [thy_expl]: "rev (app xs (Cons x Nil)) = app (rev (Cons x Nil)) (rev xs)"
by hipster_induct_simp_metis

declare [[ML_print_depth = 100]]

(* FIXME: there is something wrong going on with the simplifying part: the following is resolved
    without any issues, however it won't do so with
      by (hipster_induct_schemes revA) nor by (hipster_induct_simp_metis revA) *)
lemma revRev: "rev (rev xs) = xs"
apply (hipster_induct_simp_metis) done
(*apply(induction xs)
apply(simp_all add: revA)
done*)

lemma revApp: "rev (app xs ts) = app (rev ts) (rev xs)"
apply(induction xs ts rule: app.induct)
apply(simp_all add: revA appNil)
oops


(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
(*apply (hipster_induct_simp_metis)*)
apply(induction rs ts rule: zip.induct)
apply(simp_all)
oops

end

