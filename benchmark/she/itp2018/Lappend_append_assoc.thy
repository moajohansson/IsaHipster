(*
  Example with mixed induction and coinduction
 *)
theory Lappend_append_assoc
  imports Main "$HIPSTER_HOME/IsaHipster"
    "types/Llist"
begin
  
setup Tactic_Data.set_coinduct_sledgehammer 
  
primcorec lappend :: "'a Llist \<Rightarrow> 'a Llist \<Rightarrow> 'a Llist" where
"lnull xs \<Longrightarrow> lnull ys \<Longrightarrow> lnull (lappend xs ys)"
| "lhd (lappend xs ys) = lhd (if lnull xs then ys else xs)"
| "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"

fun to_llist :: "'a list \<Rightarrow> 'a Llist" where
  "to_llist [] = LNil"
| "to_llist (Cons x xs) = LCons x (to_llist xs)"

(* cohipster lappend append to_llist
produced these lemmas and proofs in ca. 80 seconds*)
lemma lemma_a [thy_expl]: "lappend y LNil = y"
  by (coinduction arbitrary: y rule: Llist.coinduct_strong)
    simp

lemma lemma_aa [thy_expl]: "lappend LNil y = y"
 by (coinduction arbitrary: y rule: Llist.coinduct_strong)
    simp

lemma lemma_ab [thy_expl]: "ltl (lappend y y) = lappend (ltl y) y"
 by (coinduction arbitrary: y rule: Llist.coinduct_strong)
    (metis lappend.simps(4) lemma_a lnull_def)

lemma lemma_ac [thy_expl]: "lappend (LCons y z) x2 = LCons y (lappend z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    simp

lemma lemma_ad [thy_expl]: "lappend (lappend y z) x2 = lappend y (lappend z x2)"
 by (coinduction arbitrary: x2 y z rule: Llist.coinduct_strong)
    auto

lemma lemma_ae [thy_expl]: "ltl (lappend y (ltl y)) = lappend (ltl y) (ltl y)"
 by (coinduction arbitrary: y rule: Llist.coinduct_strong)
    (metis Llist.sel(2) lappend.ctr(1) lappend.simps(4) lnull_def)

lemma lemma_af [thy_expl]: "lappend (to_llist y) (to_llist z) = to_llist (y @ z)"
apply (induct y arbitrary: z)
apply (simp add: lemma_aa)
apply (simp add: lappend.code)
  done

end