theory Dev
imports HOL_IsaP
uses "../ProofTools.ML"

begin
(* uses "../HipSpec.ML"
*)


datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree""'a Tree"
ML{*
InductDTac.induct_tac;
InductDTac.inductable_things_in_term;
val trm = @{term "x :: 'a Tree"};

val vs = ProofTools.inductable_things_in_term @{theory} trm;

val (x,ty) = Term.dest_Free trm;
val s = x ^ " :: ";
*}

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
val thy = @{theory};
val ctxt = @{context};
val trm = @{term "mirror(mirror x) = x"};

val conj = (Goal.init o (Thm.cterm_of thy) o (Syntax.read_prop ctxt)) "mirror(mirror x) = x";
val conj2 = (Goal.init o (Thm.cterm_of thy) o (Syntax.read_prop ctxt)) "x @ y = y @ x";
val vars = map fst (fst (ProofTools.inductable_things_in_sg 1 conj2));
InductDTac.induct_tac NONE [hd vars] conj2
(*
val s1 = Seq.list_of((InductDTac.induct_tac NONE vars conj2));

val s1 = Seq.list_of(Seq.maps (ProofTools.prove @{simpset}) (InductDTac.induct_tac NONE vars conj));

val t1 = (Induct_Tacs.induct_tac ctxt [[SOME "x :: 'a Tree"]] 1 conj);
val [t2] = Seq.list_of(Seq.maps (ProofTools.prove @{simpset}) t1);
Goal.finish @{context} t2;
*)
*}


ML{*
val c = ProofTools.mk_conjs @{context} ["[x] = toList(Leaf x)", "[] = toList(Leaf x)"];
val x  = ProofTools.hipspec_loop c;
*}

ML{*
val (ProofTools.ConjQ x) = the x;
val [thm] = (#proved x);
Goal.finish @{context} thm;
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
 
