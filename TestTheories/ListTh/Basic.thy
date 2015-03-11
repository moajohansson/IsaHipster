theory BasicL
imports Main
        ../Listing

begin
print_rules
print_induct_rules
ML {* Outer_Syntax.improper_command *}
ML {* Datatype.get_info *}


(*hipster_cond notNil maps tail init len*)
lemma lemma_a [thy_expl]: "tail (maps x2 y2) = maps x2 (tail y2)"
(* by (hipster_induct_simp_metis Listing.notNil.simps Listing.maps.simps Listing.tail.simps Listing.init.simps Listing.len.simps) *)
apply(induction y2)
print_cases
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
apply(induction ts rule: init.induct)
apply(simp_all)
done

lemma lastDef: "\<not> notNil ts \<Longrightarrow> last (Cons t ts) = t"
by (hipster_induct_simp_metis Listing.notNil.simps Listing.last.simps)

(* auxiliary *)
lemma noElems: "count t Nil = Z"
by simp

lemma appNil: "app ts Nil = ts"
by (hipster_induct_simp_metis Listing.app.simps )

lemma initLast: "notNil ts \<Longrightarrow> app (init ts) (Cons (last ts) Nil) = ts"
apply(induction ts rule: init.induct)
apply(simp_all)
done



lemma setCountRev: "count t ts = count t (rev ts)"
oops

lemma initLast: "notNil ts \<Longrightarrow> app (init ts) (last ts) = ts"
oops

lemma initApp: "notNil ts \<Longrightarrow> init (app rs ts) = app rs (init ts)"
apply(induction rs rule: init.induct)
apply(simp_all)
apply(case_tac ts)
apply(simp_all)
done

lemma initAppNil: "\<not> notNil ts \<Longrightarrow> init (app rs ts) = init rs"
by (hipster_induct_simp_metis Listing.notNil.simps Listing.app.simps Listing.init.simps appNil)
(* before: apply(induction ts rule: init.induct) apply(simp_all add: appNil) *)

lemma lastApp: "notNil ts \<Longrightarrow> last (app rs ts) = last ts"
apply(induction rs rule: last.induct)
apply(simp_all)
apply(case_tac ts)
apply(simp_all)
done

lemma lastAppNil: "\<not> notNil ts \<Longrightarrow> last (app rs ts) = last rs"
by (hipster_induct_simp_metis appNil) (* needs it! *)

lemma lastCons: "notNil ts \<Longrightarrow> last (Cons t ts) = last ts"
by (hipster_induct_simp_metis)

lemma countDiff: "\<not> eqN r t \<Longrightarrow> count r (app (Cons t Nil) ts) = count r ts"
by (hipster_induct_simp_metis)

lemma countInc: "eqN r t \<Longrightarrow> count r (Cons t ts) = S (count r ts)"
by (hipster_induct_simp_metis)

lemma dropNil: "drop n Nil = Nil"
apply(case_tac n)
apply(simp_all)
done
(* by (hipster_induct_simp_metis Listing.drop.simps) claims:
  Proved a different theorem:
  Listing.drop n Listing.List.Nil = Listing.List.Nil 
FIXME: why?*)

lemma dropMapComm: "drop n (maps f ts) = maps f (drop n ts)"
apply(induction ts rule: drop.induct)
apply(simp_all)
done

lemma takeMapCom: "take n (maps f ts) = maps f (take n ts)"
apply(induction ts rule: drop.induct) (* XXX: either works! drop.induct OR take.induct *)
apply(simp_all)
done

end
