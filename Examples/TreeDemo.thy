theory TreeDemo
imports Main
uses "../HipSpec.ML"

begin

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

fun map :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "map f (Leaf x) = Leaf (f x)"
| "map f (Node l r) = Node (map f l) (map f r)" 

datatype Unit = Unit

lemma "Unit=hd([])" 
sledgehammer
by (metis (full_types) Unit.exhaust)

lemma "mirror_mirror": "mirror (mirror a) = a"
apply (induct a)
sledgehammer
apply (metis mirror.simps(1))
sledgehammer
by (metis mirror.simps(2))

by (induct a, simp_all)

lemma "map_mirror": "map a (mirror a1) = mirror (map a a1)"
  apply (tactic {* HipSpec.hipspec *})
apply (induct a1, simp_all)
done





ML{*
val r = HipSpec.call_hipspec @{theory} hipspecifyer_cmd consts;
(* HipSpec.quickspec @{theory} hipspecifyer_cmd filepath modulenm consts; *)
*}




 

