(*
  Example with mixed induction and coinduction
 *)
theory Lappend_append_assoc
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

fun to_llist :: "'a list \<Rightarrow> 'a Llist" where
  "to_llist [] = LNil"
| "to_llist (Cons x xs) = LCons x (to_llist xs)"

(* hipster lappend append to_llist *)
lemma lemma_a [thy_expl]: "lappend y LNil = y"
  apply (coinduction  arbitrary: y rule: Lappend_append_assoc.Llist.coinduct_strong)
  apply simp
  done
    
lemma lemma_aa [thy_expl]: "lappend LNil y = y"
  apply (coinduction  arbitrary: y rule: Lappend_append_assoc.Llist.coinduct_strong)
apply simp
  done
    
lemma lemma_ab [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
  apply (coinduction  arbitrary: y rule: Lappend_append_assoc.Llist.coinduct_strong)
  apply (metis lappend.simps(4) lemma_a lnull_def)
  done
    
lemma lemma_ac [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
  apply (coinduction  arbitrary: x2 y z rule: Lappend_append_assoc.Llist.coinduct_strong)
  apply simp
  done
    
lemma lemma_ad [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
  apply (coinduction  arbitrary: x2 y z rule: Lappend_append_assoc.Llist.coinduct_strong)
  apply auto
  done
    
lemma lemma_ae [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
  apply (coinduction  arbitrary: y rule: Lappend_append_assoc.Llist.coinduct_strong)
  apply (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)
  done

(* Note that this lemma is proved by induction, and uses other lemmas that were discovered
   and proved by coinduction within the same proof loop. *)
lemma lemma_af [thy_expl]: "lappend (to_llist y) (to_llist z) = to_llist (y @ z)"
  apply (induct y arbitrary: z)
  apply simp
  apply (simp add: lemma_aa)
  apply simp
  apply (simp add: lemma_ac)
  done
    
end