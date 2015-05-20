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
(*hipster butlast append*)
lemma lemma_a [thy_expl]: "prop_49.append x2 Nil2 = x2"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma lemma_aa [thy_expl]: "prop_49.append (prop_49.append x2 x2) x2 =
prop_49.append x2 (prop_49.append x2 x2)"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma lemma_ab [thy_expl]: "prop_49.append (prop_49.append x2 y2) x2 =
prop_49.append x2 (prop_49.append y2 x2)"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma lemma_ac [thy_expl]: "prop_49.append (prop_49.append x2 y2) y2 =
prop_49.append x2 (prop_49.append y2 y2)"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma lemma_ad [thy_expl]: "prop_49.append (prop_49.append x2 x2) y2 =
prop_49.append x2 (prop_49.append x2 y2)"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma lemma_ae [thy_expl]: "prop_49.append (prop_49.append x2 y2) z2 =
prop_49.append x2 (prop_49.append y2 z2)"
by (hipster_induct_schemes prop_49.butlast.simps prop_49.append.simps)

lemma unknown [thy_expl]: "prop_49.butlast (prop_49.append x x) = prop_49.append x (prop_49.butlast x)"
oops

(*hipster butlastConcat butlast append*)

  theorem x0 :
    "(butlast (append xs ys)) = (butlastConcat xs ys)"
    apply(hipster_induct_schemes append.simps butlastConcat.simps butlast.simps list.exhaust thy_expl)
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
hipspec --isabelle-mode --extra-trans append --extra-trans butlast --extra-trans butlastConcat  ~/Field/thesis/IsaHipster/GenCode/prop_49_hipspec.hs - H ~/Field/thesis/IsaHipster/GenCode/prop_49.hs ~/Field/thesis/IsaHipster/GenCode/prop_49_hipspec.hs 
Trivial proof: butlastConcat Nil2 Nil2 = Nil2 
Rule: prop_49.butlast.induct 
 - vars: ["x"] 
Rule: prop_49.butlastConcat.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
Proved: butlastConcat Nil2 x = prop_49.butlast x; Saving to ThyExpl_Data: butlastConcat Nil2 ?x3 = prop_49.butlast ?x3 
Rule: prop_49.butlastConcat.induct 
 - vars: ["x"] 
Rule: prop_49.butlast.induct 
 - vars: ["x"] 
Rule: prop_49.append.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
Proved: prop_49.append x (prop_49.butlast x) = butlastConcat x x; Saving to ThyExpl_Data: prop_49.append ?x2 (prop_49.butlast ?x2) = butlastConcat ?x2 ?x2
Rule: prop_49.butlastConcat.induct 
 - vars: ["x"] 
Rule: prop_49.append.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
Failed proving: butlastConcat x (prop_49.append x x) = prop_49.append x (butlastConcat x x) 
Rule: prop_49.butlastConcat.induct 
 - vars: ["x"] 
Rule: prop_49.append.induct 
 - vars: ["x"] 
Rule: prop_49.butlast.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
induct_on: x; otherfrees:  
Failed proving: prop_49.butlast (prop_49.append x x) = butlastConcat x x 
Rule: prop_49.butlast.induct 
 - vars: ["x"] 
Rule: prop_49.butlastConcat.induct 
 - vars: ["x"] 
Rule: none 
 - vars: ["x"] 
induct_on: x; otherfrees:  
induct_on: x; otherfrees: 
end
