theory TreeDemo
imports "../IsaHipster"

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


(* First call to Hipster: Explore tmap and mirror *)
hipster mirror tmap 
lemma lemma_a [thy_expl]: "mirror (tmap x2 y2) = tmap x2 (mirror y2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeDemo.mirror.simps TreeDemo.tmap.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "mirror (mirror x2) = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeDemo.mirror.simps TreeDemo.tmap.simps thy_expl} *})


fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = [x]"
| "flat_tree (Node l r) = (flat_tree l) @ (flat_tree r)"


(* Second call to Hipster: Explore relation to lists *)
hipster flat_tree mirror tmap rev map
lemma lemma_ab [thy_expl]: "flat_tree (tmap x2 y2) = map x2 (flat_tree y2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeDemo.flat_tree.simps TreeDemo.mirror.simps TreeDemo.tmap.simps List.rev.simps List.map.simps thy_expl} *})

lemma lemma_ac [thy_expl]: "flat_tree (mirror x2) = rev (flat_tree x2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeDemo.flat_tree.simps TreeDemo.mirror.simps TreeDemo.tmap.simps List.rev.simps List.map.simps thy_expl} *})


fun rigthmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rigthmost (Leaf x) = x"
|  "rigthmost (Node l r) = rigthmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
| "leftmost (Node l r) = leftmost l"

(* If we store the tactics in a Proof_Data, then we need to explicitly pass a context around *)
ML {*val myctxt = Tactic_Data.set_induct_simp @{context} *}

ML {*Tactic_Data.hard_tac_str myctxt []; *}

(* Third call to Hipster: Rightmost and Leftmost element of a tree. *)
hipster hd rev mirror flat_tree rigthmost leftmost
lemma lemma_ad [thy_expl]: "rigthmost (mirror x2) = leftmost x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms List.hd.simps List.rev.simps TreeDemo.mirror.simps TreeDemo.flat_tree.simps TreeDemo.rigthmost.simps TreeDemo.leftmost.simps thy_expl} *})

lemma lemma_ae [thy_expl]: "hd (xs2 @ xs2) = hd xs2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms List.hd.simps List.rev.simps TreeDemo.mirror.simps TreeDemo.flat_tree.simps TreeDemo.rigthmost.simps TreeDemo.leftmost.simps thy_expl} *})

lemma unknown [thy_expl]: "hd (flat_tree x) = leftmost x"
oops



(* FIXME: Bug in translation? *)
(*
fun size :: "'a Tree \<Rightarrow> nat"
where
  "size (Leaf x) = 0"
  | "size (Node l r) = (size l + size r + 1)"
fun size1 :: "'a Tree \<Rightarrow> nat"
where
  "size1 (Leaf x) = 1"
  | "size1 (Node l r) = (size1 l + size1 r)"
ML{* Hipster_Explore.explore  @{context} ["TreeDemo.size", "TreeDemo.size1"] *}
*)

hipster last rev mirror flat_tree 
                                          "TreeDemo.rigthmost" "TreeDemo.leftmost"
lemma lemma_af [thy_expl]: "last (xs2 @ xs2) = last xs2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms List.last.simps List.rev.simps TreeDemo.mirror.simps TreeDemo.flat_tree.simps TreeDemo.rigthmost.simps TreeDemo.leftmost.simps thy_expl} *})

lemma unknown [thy_expl]: "last (flat_tree x) = rigthmost x"
oops

end
