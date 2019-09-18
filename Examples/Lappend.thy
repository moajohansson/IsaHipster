theory Lappend
  imports Main 
  "~~/src/HOL/Library/Simps_Case_Conv"
  "$HIPSTER_HOME/IsaHipster"
  
begin
setup Tactic_Data.set_sledgehammer_coinduct
setup Misc_Data.set_noisy
  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"

primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

simps_of_case lappend_simps: lappend.code
cohipster lappend
lemma lemma_a [thy_expl]: "lappend LNil y = y"
  by (simp add: lappend_simps lnull_def)

lemma lemma_aa [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
by (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)
  
lemma lemma_ab [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
  by (simp add: lappend_simps)

lemma lemma_ac [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
  by (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)
    
lemma lemma_ad [thy_expl]: "ltl (lappend y (ltl (ltl y))) = lappend (ltl y) (ltl (ltl y))"
by (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)
  
lemma lemma_ae [thy_expl]: "ltl (lappend y (ltl (ltl (ltl y)))) = lappend (ltl y) (ltl (ltl (ltl y)))"
  by (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)

lemma unknown [thy_expl]: "lappend y LNil = y"
  oops
    
lemma unknown [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
  oops
    
lemma unknown [thy_expl]: "ltl (lappend z (lappend y z)) = lappend (ltl (lappend z y)) z"
oops
  
lemma unknown [thy_expl]: "ltl (lappend y (lappend z z)) = lappend (ltl (lappend y z)) z"
  oops

lemma unknown [thy_expl]: "ltl (lappend z (lappend y (ltl z))) = lappend (ltl (lappend z y)) (ltl z)"
  oops
    
lemma unknown [thy_expl]: "ltl (lappend y (lappend z (ltl z))) = lappend (ltl (lappend y z)) (ltl z)"
  oops
    
lemma unknown [thy_expl]: "ltl (lappend y (lappend (ltl y) z)) = lappend (ltl y) (ltl (lappend y z))"
  oops

(*lemma thingy: "ltl (lappend z (lappend y z)) = lappend (ltl (lappend z y)) z"
  apply(coinduction arbitrary: y z rule: Llist.coinduct_strong)
  apply simp*)

end