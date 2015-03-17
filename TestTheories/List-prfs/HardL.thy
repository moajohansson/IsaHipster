theory HardL
imports MediumL
        "../Sorting"

begin

lemma setCountSort: "count t ts = count t (isort ts)"
oops

lemma elemIns[thy_expl] : "\<not> eqN r t \<Longrightarrow> elem r (insert t ts) = elem r ts"
by hipster_induct_simp_metis

lemma subLCount[thy_expl] : "leq (count t ts) (len ts)"
by (hipster_induct_schemes succIncreasesL)
(* apply(induction t ts rule: count.induct)
apply(simp_all add: succIncreasesL)*)

(*lemma count2 : "leq (add (count t ts) (count r ts)) (len ts)"
apply (hipster_induct_schemes count03 subLCount)*)


lemma symList[thy_expl]  : "ts = rev ts \<Longrightarrow> app (rev (drop n ts)) (rev (take n ts)) = ts"
(*apply (hipster_induct_schemes dropTake)*)
oops

lemma insLen[thy_expl] : "len (insert t ts) = S (len ts)"
by hipster_induct_simp_metis (*
apply(induction ts)
apply(simp_all)
oops*)

lemma lenIsort[thy_expl] : "len (isort ts) = len ts"
by (hipster_induct_simp_metis insLen)


(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma appZips [thy_expl] : "len a = len b \<Longrightarrow> app (zip a b) (zip c d) = zip (app a c) (app b d)"
apply(induction a b rule: zip.induct)
apply(simp_all)
apply(drule len0)
by (simp_all)

lemma auxRev [thy_expl] : "rev (rev (Cons a Nil)) = Cons a Nil"
by (tactic {* Tactic_Data.routine_tac @{context} *})

lemma revA [thy_expl] : "rev (app xs (Cons x Nil)) = app (rev (Cons x Nil)) (rev xs)"
by hipster_induct_simp_metis

declare [[ML_print_depth = 100]]

(* FIXME: there is something wrong going on with the simplifying part: the following is resolved
    without any issues, however it won't do so with
      by (hipster_induct_schemes revA) nor by (hipster_induct_simp_metis revA) *)
lemma revRev [thy_expl] : "rev (rev xs) = xs"
apply (hipster_induct_simp_metis revA) done
(*apply(induction xs)
apply(simp_all add: revA)
done*)

hipster rev app
lemma lemma_ab [thy_expl]: "app (app (x2\<Colon>'a\<Colon>type List) (y2\<Colon>'a\<Colon>type List))
 x2 =
app x2 (app y2 x2)"
by (hipster_induct_schemes Listing.rev.simps Listing.app.simps)

lemma lemma_ad [thy_expl]: "app (app (x2\<Colon>'a\<Colon>type List) (y2\<Colon>'a\<Colon>type List))
 y2 =
app x2 (app y2 y2)"
by (hipster_induct_schemes Listing.rev.simps Listing.app.simps)

lemma lemma_ae [thy_expl]: "app (app (x2\<Colon>'a\<Colon>type List) x2)
 (y2\<Colon>'a\<Colon>type List) =
app x2 (app x2 y2)"
by (hipster_induct_schemes Listing.rev.simps Listing.app.simps)

lemma unknown [thy_expl]: "app (app (x\<Colon>'a\<Colon>type List) (y\<Colon>'a\<Colon>type List))
 (z\<Colon>'a\<Colon>type List) =
app x (app y z)"
oops

lemma unknown [thy_expl]: "app (Listing.rev (x\<Colon>'a\<Colon>type List))
 (Listing.rev (y\<Colon>'a\<Colon>type List)) =
Listing.rev (app y x)"
oops

lemma unknown [thy_expl]: "app (Listing.rev (x\<Colon>'a\<Colon>type List)) (Listing.rev x) =
Listing.rev (app x x)"
oops

lemma revApp: "rev (app xs ts) = app (rev ts) (rev xs)"
apply(induction xs ts rule: app.induct)
apply(simp_all add: revA appNil)
oops

lemma s : "t = rev t \<Longrightarrow> rev (app t t) = app (rev t) (rev t)"
apply(hipster_induct_schemes revA appNil)

(* XXX: DO NOT RUN with hipster_induct_schemes *)
lemma revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
(*apply (hipster_induct_simp_metis)*)
apply(induction rs ts rule: zip.induct)
apply(simp_all)
oops

end

