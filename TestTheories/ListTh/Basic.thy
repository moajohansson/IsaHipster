theory BasicL
imports Main
        ../Listing

begin

(*hipster_cond notNil maps tail init len*)
lemma lemma_a [thy_expl]: "tail (maps x2 y2) = maps x2 (tail y2)"
(* by (hipster_induct_simp_metis Listing.notNil.simps Listing.maps.simps Listing.tail.simps Listing.init.simps Listing.len.simps) *)
apply(induction y2)
apply(simp_all)
done

lemma lemma_aa [thy_expl]: "len (maps x2 y2) = len y2"
(* by (hipster_induct_simp_metis Listing.notNil.simps Listing.maps.simps Listing.tail.simps Listing.init.simps Listing.len.simps) *)
apply(induction y2)
apply(simp_all)
done

lemma lemma_ac [thy_expl]: "notNil (maps x2 y2) = notNil y2"
(* by (hipster_induct_simp_metis Listing.notNil.simps Listing.maps.simps Listing.tail.simps Listing.init.simps Listing.len.simps) *)
apply(induction y2)
apply(simp_all)
done

(* internally goes into conditional which Hipster cannot solve right now *)
lemma unknown01 [thy_expl]: "init (maps x y) = maps x (init y)"
apply(induction y)
apply(simp_all)
apply(case_tac y)
apply(simp_all)
done

lemma auxNilIn : "\<not> (notNil x) \<Longrightarrow> init x = tail x"
apply(induction x)
apply(simp, simp)
done

lemma unknown02 [thy_expl]: "init (tail x) = tail (init x)"
apply(induction x)
apply(simp_all)
apply(case_tac x)
apply(simp_all)
done

lemma unknown03 [thy_expl]: "len (init x) = len (tail x)"
apply(induction x)
apply(simp_all)
apply(case_tac x)
apply(simp_all)
done

lemma unknown04 [thy_expl]: "notNil (init x) = notNil (tail x)"
apply(case_tac x)
apply(simp_all)
apply(case_tac List)
apply(simp_all)
done

lemma initDef: "init (app ts (Cons t Nil)) = ts"
oops

lemma lastDef: "\<not> notNil ts \<Longrightarrow> last (Cons t ts) = t"
oops

lemma setCountRev: "count t ts = count t (rev ts)"
oops

lemma initLast: "notNil ts \<Longrightarrow> app (init ts) (last ts) = ts"
oops

lemma initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
oops

lemma initAppNil: "\<not> notNil ts \<Longrightarrow> init (app rs ts) = init rs"
oops

lemma lastApp: "notNil ts \<Longrightarrow> last (app rs ts) = last ts"
oops

lemma lastAppNil: "\<not> notNil ts \<Longrightarrow> last (app rs ts) = last rs"
oops

lemma lastCons: "notNil ts \<Longrightarrow> last (Cons t ts) = last ts"
oops

lemma countDiff: "\<not> eqN r t \<Longrightarrow> count r (app (Cons t Nil) ts) = count r ts"
oops

lemma countInc: "eqN r t \<Longrightarrow> count r (Cons t ts) = S (count r ts)"
oops

lemma dropMapComm: "drop n (map f ts) = map f (drop n ts)"
oops

lemma takeMapCom: "take n (map f ts) = map f (take n ts)"
oops

end
