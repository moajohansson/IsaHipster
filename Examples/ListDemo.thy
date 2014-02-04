theory ListDemo
(* imports HOL_IsaP *)
imports Main
uses "../HipSpec.ML" 

begin

datatype 'a Lst = 
  Emp
  | Cons "'a" "'a Lst"

primrec hd :: "'a Lst \<Rightarrow> 'a"
where
  "hd (Cons x xs) = x"

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


ML {* val consts = ["ListDemo.app", "ListDemo.rev" (*, "ListDemo.qrev" *)] ; *}
ML {* 
val (thms,s, fails) = HipSpec.hipspec_explore @{theory} consts;
*}
ML{*
val mymetis = Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.metis_default_lam_trans;
*}
lemma app_nil[simp]: "app xs Emp = xs"
apply (induct xs)
apply simp_all
done

lemma app_assoc[simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply (induct xs)
apply simp_all
done
ML{*

*}
lemma rev_app_2: "app (rev ys) (rev xs) =  rev (app xs ys)"
apply (induct xs)
apply simp
apply (metis rev.simps app.simps app_assoc)
apply (drule sym)
apply simp
done

lemma "rev(rev xs) = xs"
apply (induct xs)
apply simp
apply (simp add:rev_app_2)
apply (metis rev.simps app.simps app_assoc rev_app_2)

ML{* 
val [f] = fails;


val f4 = Seq.hd (rtac (sym) 1 f); 

val res = (ALLGOALS (ProofTools.induct_on_goal s)) f4;
Seq.pull res;
*}

ML{*

Pretty.str_of;
map Pretty.writeln (map ((Syntax.pretty_term @{context}) o prop_of) thms);

*}
thm sym

theorem "mythm" : "app (app x y) z = app x (app y z)"
apply (rule sym)
apply (tactic  {*ProofTools.prove_by_simp s*})
done
lemma "app (app x y) x = app x (app y x)"
by (simp add : mythm)

lemma "rev xs = qrev xs Emp"
apply (induct xs)
apply simp
apply simp
(*apply (tactic {* (HipSpec.hipspec_explore_tac consts) *}) *)
sorry


lemma "app x Emp = x"

apply (tactic {*ProofTools.prove_by_simp s*})
done

ML{*
 Isabelle_System.bash;
val lemmas = 
"qrev x Emp = rev x\napp x Emp = x\n qrev (qrev x y) z = qrev y (app x z)\n qrev (app x y) z = qrev y (qrev x z)\n app (qrev x y) z = qrev x (app y z)\n";

val lem_list = Library.split_lines lemmas;

ProofTools.hipspec_loop @{context} lemmas;
*}

end