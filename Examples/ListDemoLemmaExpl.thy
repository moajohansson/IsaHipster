theory ListDemoLemmaExpl
imports "$HIPSTER_HOME/IsaHipster"
begin
ML\<open>
Goal.prove; Variable.auto_fixes

\<close>

ML Thm.assume

ML\<open>

val t = Thm.assume @{cprop "x = x"};

(* Handle binding stuff in context for just proof *)
fun f ctxt = Goal.prove ctxt ["x"] [@{prop True}] @{prop "x = x"}
  (fn args => no_tac) handle ERROR _ => TrueI

val r = f @{context}

\<close>

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"


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
lemma lemma_a [thy_expl]: "app a Emp = a"
  apply lemma_explore
  apply (induct a)
  apply simp
  apply simp
  done

lemma lemma_aa [thy_expl]: "app (app y z) x2 = app y (app z x2)"
  apply (induct y arbitrary: x2 z)
  apply simp
  apply simp
  done


 hipster rev app
lemma lemma_ab [thy_expl]: "app (ListDemoLemmaExpl.rev z) (ListDemoLemmaExpl.rev y) = ListDemoLemmaExpl.rev (app y z)"
  apply (induct y arbitrary: z)
  apply simp
  apply (simp add: lemma_a)
  apply simp
apply (metis lemma_aa)
  done
    
lemma lemma_ac [thy_expl]: "ListDemoLemmaExpl.rev (Lst.Cons z (ListDemoLemmaExpl.rev y)) = app y (Lst.Cons z Emp)"
  apply (induct y)
  apply simp
apply simp
  apply (metis ListDemoLemmaExpl.rev.simps(1) ListDemoLemmaExpl.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
  done
    
lemma lemma_ad [thy_expl]: "ListDemoLemmaExpl.rev (app z (ListDemoLemmaExpl.rev y)) = app y (ListDemoLemmaExpl.rev z)"
  apply (induct y arbitrary: z)
  apply simp
apply (simp add: lemma_a)
apply simp
apply (metis ListDemoLemmaExpl.rev.simps(1) ListDemoLemmaExpl.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
done 

(*lemma lemma_ab [thy_expl]: "app (ListDemo.rev x5) (ListDemo.rev y5) = ListDemo.rev (app y5 x5)"
apply (induct y5)
sledgehammer
apply (metis ListDemo.rev.simps(1) app.simps(1) lemma_a)
sledgehammer
by (metis ListDemo.rev.simps(2) app.simps(2) lemma_aa)
*)

theorem rev_rev : "rev(rev xs) = xs "
  apply (induct xs)
  apply simp
  apply simp
  apply (metis ListDemoLemmaExpl.rev.simps(1) ListDemoLemmaExpl.rev.simps(2) app.simps(1) app.simps(2) lemma_ab)
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

ML\<open>Hipster_Explore.explore @{context} ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev"];
\<close>
lemma lemma_a' [thy_expl]: "app x2 Emp = x2"
by (tactic \<open>Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl}\<close>)

lemma lemma_aa' [thy_expl]: "qrev (qrev x2 y2) z2 = qrev y2 (app x2 z2)"
by (tactic \<open>Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl}\<close>)

lemma lemma_ab' [thy_expl]: "qrev (ListDemo.rev x5) y5 = app x5 y5"
by (tactic \<open>Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl}\<close>)
thm thy_expl


setup \<open>Hipster_Explore.setup_exploration ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev"];
\<close>

thm thy_expl


theorem rev_qrev : "rev xs = qrev xs Emp"
apply (induct xs)
apply simp
apply simp
by (metis thy_expl qrev.simps(1))
(*
apply (tactic {* Hipster_Explore.explore_goal @{context} ["ListDemo.rev", "ListDemo.app", "ListDemo.qrev"] *}) 
*)
ML \<open>\<close>





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
by (tactic \<open>Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps ListDemo.qrev.simps thy_expl}\<close>)

end

