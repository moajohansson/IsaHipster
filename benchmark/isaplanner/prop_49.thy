theory prop_49
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
  | "butlast (Cons2 y (Nil2)) = Nil2"
  | "butlast (Cons2 y (Cons2 x2 x3)) =
       Cons2 y (butlast (Cons2 x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
  | "butlastConcat x (Cons2 z x2) = append x (butlast (Cons2 z x2))"
  (*hipster butlast append butlastConcat *)
(*hipster butlast append*)(*
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes butlast.simps append.simps)

lemma lemma_aa [thy_expl]: "append (append x2 y2) z2 = append x2 (append y2 z2)"
by (hipster_induct_schemes butlast.simps append.simps)

lemma unknown [thy_expl]: "butlast (append x x) = append x (butlast x)"
oops

lemma lemma_ab [thy_expl]: "butlastConcat Nil2 x = butlast x"
by (hipster_induct_schemes butlast.simps append.simps)

lemma lemma_ac [thy_expl]: "append x (butlast x) = butlastConcat x x"
by (hipster_induct_schemes butlast.simps append.simps)*)
(*
hipster butlast butlastConcat append
*)
(*hipster butlastConcat butlast append*)

setup{* Hip_Tac_Ops.set_metis_to @{context} 16000 *}
setup{* Hip_Tac_Ops.set_metis_filter @{context} (K false)*}

  theorem x0 :
    "(butlast (append xs ys)) = (butlastConcat xs ys)"
    apply(hipster_induct_schemes butlastConcat.simps prop_49.append.simps append.simps list.exhaust)

    apply(induction xs arbitrary:ys rule: butlast.induct)
    apply(simp_all)
    apply(metis  butlastConcat.simps butlast.simps append.simps list.exhaust)
    apply(metis  butlastConcat.simps butlast.simps append.simps list.exhaust)
    by (metis butlastConcat.simps  append.simps prop_49.butlast.simps list.exhaust)
    (*apply (metis append.elims butlastConcat.elims prop_49.append.simps(2) prop_49.butlast.simps(3) prop_49.list.distinct(1))

    apply(metis  butlastConcat.simps butlast.simps append.simps list.exhaust)*)

    (*apply(metis thy_expl butlastConcat.elims prop_49.append.simps(2) prop_49.butlast.simps(3) list.exhaust)*)


    (*apply(metis  append.simps butlast.simps butlastConcat.simps)*)

    (*apply(hipster_induct_schemes append.simps butlastConcat.simps butlast.simps list.exhaust thy_expl)*)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
hipspec --isabelle-mode --extra-trans append --extra-trans butlast --extra-trans butlastConcat  ~/Field/thesis/IsaHipster/GenCode/prop_49_hipspec.hs - H ~/Field/thesis/IsaHipster/GenCode/hs ~/Field/thesis/IsaHipster/GenCode/prop_49_hipspec.hs 
Trivial proof: butlastConcat Nil2 Nil2 = Nil2 
Rule: butlast.induct 
 - vars: ["x"] 
Rule: butlastConcat.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
Proved: butlastConcat Nil2 x = butlast x; Saving to ThyExpl_Data: butlastConcat Nil2 ?x3 = butlast ?x3 
Rule: butlastConcat.induct 
 - vars: ["x"] 
Rule: butlast.induct 
 - vars: ["x"] 
Rule: append.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
Proved: append x (butlast x) = butlastConcat x x; Saving to ThyExpl_Data: append ?x2 (butlast ?x2) = butlastConcat ?x2 ?x2
Rule: butlastConcat.induct 
 - vars: ["x"] 
Rule: append.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
Failed proving: butlastConcat x (append x x) = append x (butlastConcat x x) 
Rule: butlastConcat.induct 
 - vars: ["x"] 
Rule: append.induct 
 - vars: ["x"] 
Rule: butlast.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
Failed proving: butlast (append x x) = butlastConcat x x 
Rule: butlast.induct 
 - vars: ["x"] 
Rule: butlastConcat.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees: 
end
