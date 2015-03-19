theory HardL
imports MediumL
        "../Sorting"

begin

lemma setCountSort: "count t ts = count t (isort ts)"
oops

lemma elemIns : "\<not> eqN r t \<Longrightarrow> elem r (insert t ts) = elem r ts"
by hipster_induct_simp_metis

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
apply(induction a b rule: zip.induct)
apply(simp_all)
by (metis app.simps len.simps List.exhaust Nat.distinct)


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
by (hipster_induct_simp_metis revA')
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

lemma appRevAntiDistr [thy_expl] : "app (rev x) (rev y) = rev (app y x)"
by (hipster_induct_simp_metis appNil appAssoc)

lemma revApp: "rev (app xs ts) = app (rev ts) (rev xs)"
by (hipster_induct_simp_metis appAssoc appNil)

(* immediately follows *)
lemma s : "t = rev t \<Longrightarrow> rev (app t t) = app t t"
(*apply(hipster_induct_schemes revA appNil appAssoc)*)
by (tactic {* Tactic_Data.routine_tac @{context} *})


(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
(*apply (hipster_induct_simp_metis)*)
apply(induction rs ts rule: zip.induct)
apply(simp_all)
oops

end

