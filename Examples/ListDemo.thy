theory ListDemo
imports "../IsaHipster"
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

lemma lemma_a [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps ListDemo.qrev.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "qrev (qrev x2 y2) z2 = qrev y2 (app x2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.rev.simps ListDemo.app.simps ListDemo.qrev.simps thy_expl} *})

theorem rev_qrev : "rev xs = qrev xs Emp"
apply (induct xs)
apply simp
apply simp

apply (tactic {* Hipster_Explore.explore_goal @{context} ["ListDemo.rev", "ListDemo.app", "ListDemo.qrev"] *}) 

(*
ML{*Hipster_Explore.explore @{context} ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev"];
 *}

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
end