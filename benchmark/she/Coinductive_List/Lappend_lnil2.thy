theory Lappend_lnil2
  imports Main "$HIPSTER_HOME/IsaHipster" "$HIPSTER_HOME/ObsIntTrans"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer  
codatatype (lset: 'a) Llist =
    lnull: LNil
    | LCons (lhd: 'a) (ltl: "'a Llist")
where
 "ltl LNil = LNil"
  
primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"
  
(*hipster lappend*)
lemma lemma_a [thy_expl]: "lappend y LNil = y"
  apply (coinduction  arbitrary: y rule: Lappend_lnil2.Llist.coinduct_strong)
by simp
    
lemma lemma_aa [thy_expl]: "lappend LNil y = y"
apply (coinduction  arbitrary: y rule: Lappend_lnil2.Llist.coinduct_strong)
by simp

lemma lemma_ab [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
apply (coinduction  arbitrary: y rule: Lappend_lnil2.Llist.coinduct_strong)
apply simp
by (smt Llist.collapse(1) Llist.sel(2) lappend.disc_iff(2) lappend.simps(3) lappend.simps(4))

lemma lemma_ac [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Lappend_lnil2.Llist.coinduct_strong)
by simp

lemma lemma_ad [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
apply (coinduction  arbitrary: x2 y z rule: Lappend_lnil2.Llist.coinduct_strong)
apply simp
by auto

lemma lemma_ae [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
apply (coinduction  arbitrary: y rule: Lappend_lnil2.Llist.coinduct_strong)
apply simp
  by (fastforce Llist.collapse(1) Llist.sel(2) lemma_a)
(* Bad arguments for method "fastforce"\<here>:
  Llist.collapse ( 1 ) Llist.sel ( 2 ) lemma_a
but works if we change fastforce to metis?
*)
 
theorem  lappend_LNil2: "lappend xs LNil = xs"
  by (simp add: lemma_a)
(*by hipster_coinduct_sledgehammer works also*)  
end