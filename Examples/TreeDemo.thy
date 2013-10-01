theory TreeDemo
(*imports Main *)
imports HOL_IsaP
uses "HipSpec.ML"

begin

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

fun tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "tmap f (Leaf x) = Leaf (f x)"
| "tmap f (Node l r) = Node (tmap f l) (tmap f r)" 



ML{*

val consts = ["mirror","tmap"];

val s = Context.theory_name @{theory}
*}


lemma "map_mirror": "tmap a (mirror a1) = mirror (tmap a a1)"
    apply (tactic {* fn thm => let val _ = (Trm.MLSerialise.print_term (Thm.concl_of thm)) in Seq.single thm end;  *})

  apply (tactic {* HipSpec.hipspec *})
apply (induct a1, simp_all)
done


(*by (induct a1, simp_all) *)
ML{* val thm = Thm.concl_of @{thm "map_mirror"}; 
val s=  (Syntax.string_of_term @{context} thm);
writeln s;
*}


ML{*
val r = HipSpec.call_hipspec @{theory} hipspecifyer_cmd consts;
(* HipSpec.quickspec @{theory} hipspecifyer_cmd filepath modulenm consts; *)
*}



lemma "mirror_mirror": "mirror (mirror a) = a"
by (induct a, simp_all)

 

