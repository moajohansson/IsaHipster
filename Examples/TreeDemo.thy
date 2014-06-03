theory TreeDemo
imports "../IsaHipster"

begin
setup{* 
Tactic_Data.set_induct_simp;
*}
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
by hipster_induct_simp

lemma lemma_aa [thy_expl]: "mirror (mirror x12) = x12"
by hipster_induct_simp

fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = [x]"
| "flat_tree (Node l r) = (flat_tree l) @ (flat_tree r)"


(* Second call to Hipster: Explore relation to lists *)
hipster flat_tree mirror tmap rev map
lemma lemma_ab [thy_expl]: "flat_tree (tmap x10 y10) = map x10 (flat_tree y10)"
by hipster_induct_simp

lemma lemma_ac [thy_expl]: "flat_tree (mirror x36) = rev (flat_tree x36)"
by hipster_induct_simp

fun rigthmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rigthmost (Leaf x) = x"
|  "rigthmost (Node l r) = rigthmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
| "leftmost (Node l r) = leftmost l"

fun nonEmpty :: "'a list => bool"
where
  "nonEmpty [] = False"
 |"nonEmpty _ = True"


(* Third call to Hipster: Rightmost and Leftmost element of a tree. Now we get both leftmost/rightmost
lemmas, as I changed it so it won't add the previous thy_expl things directly to the simp set, also 
set a rather short time limit. The time limits should be made into flags!*)
hipster hd rev mirror flat_tree rigthmost leftmost
lemma lemma_ad [thy_expl]: "rigthmost (mirror x18) = leftmost x18"
by hipster_induct_simp

lemma lemma_ae [thy_expl]: "leftmost (mirror x60) = rigthmost x60"
by hipster_induct_simp

lemma lemma_af [thy_expl]: "hd (xs186 @ xs186) = hd xs186"
by hipster_induct_simp

lemma unknown [thy_expl]: "hd (flat_tree x) = leftmost x"
oops


(* FIXME: Bug in translation? *)

fun size :: "'a Tree \<Rightarrow> nat"
where
  "size (Leaf x) = 0"
  | "size (Node l r) = (size l + size r + 1)"
fun size1 :: "'a Tree \<Rightarrow> nat"
where
  "size1 (Leaf x) = 1"
  | "size1 (Node l r) = (size1 l + size1 r)"
(*  hipster  size *) (* TO DO! Make sure + and 0,1 gets transalated back to the right constants*)
(* Issue! These constants are polymorphic! fix fix fix... *)
ML{* @{term "nonEmpty ys \<and> true ==> flat_tree x = []"} *}

(*

hipster last rev mirror flat_tree rigthmost leftmost
lemma lemma_af [thy_expl]: "last (xs2 @ xs2) = last xs2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms List.last.simps List.rev.simps TreeDemo.mirror.simps TreeDemo.flat_tree.simps TreeDemo.rigthmost.simps TreeDemo.leftmost.simps thy_expl} *})

lemma unknown [thy_expl]: "last (flat_tree x) = rigthmost x"
oops
*)
end

