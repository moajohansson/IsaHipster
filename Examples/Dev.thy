theory Dev
imports Main
uses "../ProofTools.ML"

begin
(* uses "../HipSpec.ML"
*)

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"

definition unit :: "'a => 'a Tree"
where
  "unit x =  Leaf x"

fun append :: "'a Tree => 'a Tree => 'a Tree"
where
  "append t1 t2 = Node t1 t2"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

fun map :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "map f (Leaf x) = Leaf (f x)"
| "map f (Node l r) = Node (map f l) (map f r)" 

fun toList :: "'a Tree \<Rightarrow> 'a list"
where
  "toList (Leaf a) = [a]"
  | "toList (Node l r) = (toList l) @ (toList r)"


ML{*
(*val c = ProofTools.mk_conjs @{context} ["mirror (unit x) = Leaf x"];
*)
val t = Syntax.read_term  @{context} "Trueprop([x] = toList(Leaf x))";
val ct = Thm.cterm_of (Proof_Context.theory_of @{context}) t;
val thm = Goal.init ct;

val x = Seq.hd(ProofTools.simp_all (HOL_basic_ss addsimps @{thms "toList.simps"}) thm);

*}

ML{*
val filepath = "~/TheoremProvers/IsaHip/";
val hipspecifyer_cmd = filepath^"HipSpecifyer";
val modulenm = "Tree";
val consts = ["Tree.mirror","Tree.map"];
*}


ML{*
(*
val (x, l) = Code_Target.produce_code @{theory} consts "Haskell" NONE "Tree" [] 
*)
HipSpec.call_hipspec @{theory} consts;

*}


ML{*
val app = Code_Thingol.lookup_const naming "List.append";
*}




lemma "map_mirror": "tmap a (mirror a1) = mirror (tmap a a1)"
by (induct a1, simp_all)

lemma "mirror_mirror": "mirror (mirror a) = a"
by (induct a, simp_all)
 
