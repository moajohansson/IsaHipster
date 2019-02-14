theory ListDemo
imports "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

(*
primrec hd :: "'a Lst \<Rightarrow> 'a"
where
  "hd (Cons x xs) = x"
*)
fun app :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" 
where 
  "app Emp xs = xs"
| "app (Cons x xs) ys = Cons x (app xs ys)"

 
fun rev :: "'a Lst \<Rightarrow> 'a Lst"
where 
  "rev Emp = Emp"
| "rev (Cons x xs) = app (rev xs) (Cons x Emp)"

fun qrev :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst"
where 
  "qrev Emp a = a"
| "qrev (Cons x xs) a = qrev xs (Cons x a)"

hipster app
lemma lemma_a [thy_expl]: "app y Emp = y"
  apply (induct y)
  apply simp
  apply simp
  done

lemma lemma_aa [thy_expl]: "app (app y z) x2 = app y (app z x2)"
  apply (induct y arbitrary: x2 z)
  apply simp
  apply simp
  done
(*lemma lemma_a [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "app (app x2 y2) z2 = app x2 (app y2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps thy_expl} *})
*)

hipster rev
lemma lemma_ab [thy_expl]: "app (ListDemo.rev z) (ListDemo.rev y) = ListDemo.rev (app y z)"
apply (induct y arbitrary: z)
apply (simp add: lemma_a)
apply (metis ListDemo.rev.simps(2) app.simps(2) lemma_aa)
done

lemma lemma_ac [thy_expl]: "ListDemo.rev (Lst.Cons z (ListDemo.rev y)) = app y (Lst.Cons z Emp)"
apply (induct y)
  apply simp
  apply (metis ListDemo.rev.simps(2) Lst.distinct(1) Lst.inject app.elims app.simps(1) lemma_ab rev.elims)
  done
    
lemma lemma_ad [thy_expl]: "ListDemo.rev (app z (ListDemo.rev y)) = app y (ListDemo.rev z)"
  apply (induct y arbitrary: z)
  apply (metis ListDemo.rev.simps(1) lemma_ab)
  apply (metis ListDemo.rev.simps(1) ListDemo.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
  done
(*lemma lemma_ab [thy_expl]: "app (ListDemo.rev x5) (ListDemo.rev y5) = ListDemo.rev (app y5 x5)"
apply (induct y5)
sledgehammer
apply (metis ListDemo.rev.simps(1) app.simps(1) lemma_a)
sledgehammer
by (metis ListDemo.rev.simps(2) app.simps(2) lemma_aa)
*)

theorem rev_rev : "rev(rev xs) = xs "
(* by hipster_induct*)
  apply (induct xs)
  apply simp
  apply (metis ListDemo.rev.simps(1) ListDemo.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
  done
 (* sledgehammer
  by (metis ListDemo.rev.simps(1) lemma_a lemma_ad)*)
(*apply (induct xs)
sledgehammer
(* apply (tactic {* Hipster_Explore.explore_goal @{context} ["ListDemo.rev", "ListDemo.app"] *}) *)
apply (metis ListDemo.rev.simps(1))
apply simp
sledgehammer
by (metis ListDemo.rev.simps(1) ListDemo.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
*)
(*
Try first proving lemmas:

lemma lemma_a [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "app (app x2 y2) z2 = app x2 (app y2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps thy_expl} *})

lemma lemma_ab [thy_expl]: "app (ListDemo.rev x5) (ListDemo.rev y5) = ListDemo.rev (app y5 x5)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps thy_expl} *})

then prove the open goal ListDemo.rev (ListDemo.rev xs) = xs by (tactic {*Simp_Metis_Tacs.routine_tac @{context}*})
*)

ML{*Hipster_Explore.explore @{context} ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev"];
 *}
lemma lemma_a' [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})

lemma lemma_aa' [thy_expl]: "qrev (qrev x2 y2) z2 = qrev y2 (app x2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})

lemma lemma_ab' [thy_expl]: "qrev (ListDemo.rev x5) y5 = app x5 y5"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})
thm thy_expl


setup {* Hipster_Explore.setup_exploration ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev"];
 *}

thm thy_expl


theorem rev_qrev : "rev xs = qrev xs Emp"
apply (induct xs)
apply simp
apply simp
by (metis thy_expl qrev.simps(1))
(*
apply (tactic {* Hipster_Explore.explore_goal @{context} ["ListDemo.rev", "ListDemo.app", "ListDemo.qrev"] *}) 
*)
ML {* *}





(*



lemma lemma_a [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "qrev (qrev x2 y2) z2 = qrev y2 (app x2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})

lemma lemma_ab [thy_expl]: "qrev (ListDemo.rev x5) y5 = app x5 y5"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})


lemma rev_qrev: "rev xs = qrev xs Emp"
sledgehammer
by (metis lemma_a lemma_aa lemma_ab)

lemma rev_rev : "rev(rev xs) = xs"
sledgehammer
by (metis lemma_a lemma_ab rev_qrev)


ML{* Hipster_Explore.explore @{context} ["ListDemo.qrev", "ListDemo.rev"]; *}

















lemma f
 explore
proof -
  have lemma1: f
    proof
  have lemma2: g
    proof
  from lemma1 lemma2 show ?thesis
    proof
qed


*)
lemma lemma_ab'' [thy_expl]: "qrev x5 Emp = ListDemo.rev x5"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl} *})

end

