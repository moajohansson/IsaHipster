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

ML{*Hipster_Explore.explore @{context} ["ListDemo.app"];
 *}
lemma lemma_a [thy_expl]: "app x2 Emp = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "app (app x2 y2) z2 = app x2 (app y2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps thy_expl} *})

ML{*
Hipster_Explore.explore @{context}  ["ListDemo.app", "ListDemo.rev"];
*}
lemma lemma_ab [thy_expl]: "app (ListDemo.rev x5) (ListDemo.rev y5) = ListDemo.rev (app y5 x5)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps thy_expl} *})

lemma lemma_ac [thy_expl]: "ListDemo.rev (ListDemo.rev x5) = x5"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.app.simps ListDemo.rev.simps thy_expl} *})

ML{* Hipster_Explore.explore @{context} ["ListDemo.qrev", "ListDemo.rev"]; *}
lemma lemma_ad [thy_expl]: "app (qrev x2 y2) z2 = qrev x2 (app y2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.qrev.simps ListDemo.rev.simps thy_expl} *})

lemma lemma_ae [thy_expl]: "qrev (app x2 y2) z2 = qrev y2 (qrev x2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.qrev.simps ListDemo.rev.simps thy_expl} *})

lemma lemma_af [thy_expl]: "qrev (qrev x2 y2) z2 = qrev y2 (app x2 z2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.qrev.simps ListDemo.rev.simps thy_expl} *})

lemma lemma_ag [thy_expl]: "qrev x5 (ListDemo.rev y5) = ListDemo.rev (app y5 x5)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms ListDemo.qrev.simps ListDemo.rev.simps thy_expl} *})


ML{* Hipster_Explore.explore @{context} ["ListDemo.app","ListDemo.qrev", "ListDemo.rev"]; *}
(* At this point HipSpec is done! *)

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

ML{*
open Active;
Active.sendback_markup;
*}


ML{*
HipsterRules.get @{context};
(*
   Output.urgent_message
     ("HipSpec found this proof: " ^
      Active.sendback_markup [Markup.padding_command] "by (metis rev.simps(2))" ^ ".")
*)
   *}


end