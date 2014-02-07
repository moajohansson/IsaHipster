theory ListDemo
imports "../IsaHipster"

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


ML {* val consts = ["ListDemo.app", "ListDemo.rev", "ListDemo.qrev" ] ; *}

(* NOTE: Want to replace the below slow command, with something faster, i.e. Metis with given
lemmas. Need to name lemmas and export them to the outer context to do this I think? Or,
store them in some Theory_Data structure? *)
ML{*
val ctxt = @{context};
val facts = maps (fn c => Sledgehammer_Util.thms_of_name ctxt (c^".simps")) consts
val (lems0, ctxt', fails) = HipSpec.hipspec_explore ctxt facts consts;

val [l1,l2,l3] = lems0;
val lems = [Thm.put_name_hint "hipspec1" l1, 
  Thm.put_name_hint "hipspec2" l2, Thm.put_name_hint "hipspec3" l3];
*}
ML{* 
Context.Proof;
Proof_Context.export ctxt' ctxt lems; *}

ML {* 
Context.Proof;
Proof_Context.export;
Context.theory_map;
Global_Theory.add_thms_dynamic;
Config.put_global;
HipsterRules.add_thm;
Context.>>;
Thm.put_name_hint;
*}



ML{*
val f = fn thy => (Library.foldl (fn (thy,thm) => Context.theory_map (HipsterRules.add_thm thm) thy) (thy,lems));

Context.>>
*}

thm hipster_thms

lemma "rev xs = qrev xs Emp"
apply (tactic {* ProofTools.timed_metis_tac @{context} @{thms hipster_thms} 1 *})

apply (tactic {* HipSpec.hipspec_explore_tac @{context} consts *})
done


ML {* 

val (thms,s, fails) = HipSpec.hipspec_explore @{theory} consts;

map Pretty.writeln (map ((Syntax.pretty_term @{context}) o prop_of) thms);
*}
lemma "rev(rev xs) = xs"
apply (tactic {* ProofTools.timed_metis_tac @{context} (@{thms rev.simps} @ @{thms app.simps} @ thms) 1 *})
done

lemma "app xs (app ys zs) = app (app xs ys) zs"
apply (tactic {* ProofTools.timed_metis_tac @{context} (@{thms rev.simps} @ @{thms app.simps} @ thms) 1 *})
done

lemma "rev xs = qrev xs Emp"
apply (tactic {* ProofTools.timed_metis_tac @{context} (@{thms rev.simps} @ @{thms app.simps} @ thms) 1 *})
done


ML{*

Pretty.str_of;
map Pretty.writeln (map ((Syntax.pretty_term @{context}) o prop_of) thms);

*}
ML{*
(* map (Sledgehammer_Util.thms_of_name @{context}) consts; *)

*}
lemma "rev(rev xs) = xs"
apply (induct xs)
apply simp
apply simp
apply (tactic {* mymetis @{context} (@{thms rev.simps} @ @{thms app.simps} @ thms) 1 *})


lemma app_nil[simp]: "app xs Emp = xs"
apply (tactic {* timed_metis_tac @{context} [@{thm ListDemo.rev.simps(2)}, @{thm app.simps(2)}] 1 *})
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
apply (tactic {* mymetis @{context} [@{thm ListDemo.rev.simps(2)}, @{thm app.simps(2)}, @{thm app_assoc}] 1*} )
 (* apply (metis rev.simps app.simps app_assoc)
apply (drule sym)
apply simp *)
done

lemma "rev(rev xs) = xs"
apply (induct xs)
apply simp
apply (simp add:rev_app_2)
apply (metis rev.simps app.simps app_assoc rev_app_2)



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



end