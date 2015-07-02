theory TreeSimp
imports "$HIPSTER_HOME/IsaHipster"

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


ML{* Hipster_Explore_Simp.explore  @{context} ["TreeSimp.tmap", "TreeSimp.mirror"]; *}
lemma lemma_a [thy_expl]: "mirror (tmap x2 y2) = tmap x2 (mirror y2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.tmap.simps TreeSimp.mirror.simps thy_expl} *})

lemma lemma_aa [thy_expl]: "mirror (mirror x2) = x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.tmap.simps TreeSimp.mirror.simps thy_expl} *})


fun rigthmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rigthmost (Leaf x) = x"
|  "rigthmost (Node l r) = rigthmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
|  "leftmost (Node l r) = leftmost l"

ML{* Hipster_Explore_Simp.explore  @{context} ["TreeSimp.mirror","TreeSimp.tmap", "TreeSimp.rigthmost", "TreeSimp.leftmost"]; *}
lemma lemma_ab [thy_expl]: "leftmost (mirror x2) = rigthmost x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.rigthmost.simps TreeSimp.leftmost.simps thy_expl} *})

lemma lemma_ac [thy_expl]: "rigthmost (mirror x2) = leftmost x2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.rigthmost.simps TreeSimp.leftmost.simps thy_expl} *})

fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = Cons x []"
| "flat_tree (Node l r) = (flat_tree l) @ (flat_tree r)"


ML{*Hipster_Explore_Simp.explore  @{context} ["TreeSimp.flat_tree", "TreeSimp.mirror", "TreeSimp.tmap", "TreeSimp.leftmost", "TreeSimp.rigthmost","List.rev", "List.map", "List.hd", "List.append"]; *}

lemma lemma_ad [thy_expl]: "flat_tree (tmap x2 y2) = map x2 (flat_tree y2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.flat_tree.simps TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.leftmost.simps TreeSimp.rigthmost.simps List.rev.simps List.append.simps thy_expl} *})

lemma lemma_ae [thy_expl]: "map x2 (rev xs2) = rev (map x2 xs2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.flat_tree.simps TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.leftmost.simps TreeSimp.rigthmost.simps List.rev.simps List.append.simps thy_expl} *})

lemma lemma_af [thy_expl]: "flat_tree (mirror x2) = rev (flat_tree x2)"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.flat_tree.simps TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.leftmost.simps TreeSimp.rigthmost.simps List.rev.simps List.append.simps thy_expl} *})

lemma lemma_ag [thy_expl]: "hd (xs2 @ xs2) = hd xs2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms TreeSimp.flat_tree.simps TreeSimp.mirror.simps TreeSimp.tmap.simps TreeSimp.leftmost.simps TreeSimp.rigthmost.simps List.rev.simps List.append.simps thy_expl} *})

lemma unknown [thy_expl]: "hd (flat_tree x) = leftmost x"
apply (tactic {* Hipster_Explore.explore_goal @{context} ["TreeSimp.flat_tree", "TreeSimp.leftmost"] *}) 
by (hipster_induct_simp_metis flat_tree.simps)
oops


end
