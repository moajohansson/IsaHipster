theory TreeDemo
imports "../IsaHipster"

begin

(* FIXME: Simp-rules for map and hd have new names in Isabelle2014. We can't rely on 
function_name.simps in all cases. This needs to be fixed. When just using simp it doesn't
matter, but Metis needs to be fed the desired lemmas. Investigate how to select the relevant ones,
and also, how to only get the neccesary ones to paste into proof-script.
*)
setup Tactic_Data.set_induct_simp

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
hipster tmap mirror
lemma lemma_a [thy_expl]: "mirror (tmap x2 y2) = tmap x2 (mirror y2)"
by hipster_induct_simp

lemma lemma_aa [thy_expl]: "mirror (mirror x2) = x2"
by hipster_induct_simp


fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = [x]"
| "flat_tree (Node l r) = (flat_tree l) @ (flat_tree r)"


(* Second call to Hipster: Explore relation to lists: flat_tree tmap mirror rev map *)
hipster flat_tree tmap mirror rev map
lemma lemma_ab [thy_expl]: "flat_tree (tmap x2 y2) = map x2 (flat_tree y2)"
by hipster_induct_simp

lemma lemma_ac [thy_expl]: "flat_tree (mirror x2) = rev (flat_tree x2)"
by hipster_induct_simp

fun rightmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rightmost (Leaf x) = x"
| "rightmost (Node l r) = rightmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
| "leftmost (Node l r) = leftmost l"

(* Third call to Hipster: hd mirror flat_tree  rightmost leftmost*)
hipster hd mirror flat_tree rightmost leftmost
lemma lemma_ad [thy_expl]: "leftmost (mirror x2) = rightmost x2"
by hipster_induct_simp

lemma lemma_ae [thy_expl]: "rightmost (mirror x2) = leftmost x2"
by hipster_induct_simp

lemma lemma_af [thy_expl]: "hd (xs2 @ xs2) = hd xs2"
by hipster_induct_simp


lemma nonEmp[simp]: "flat_tree t ~= []"
by (hipster_induct_simp)

lemma unknown [thy_expl]: "hd (flat_tree x) = leftmost x"
by (hipster_induct_simp)































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
*)
(*  hipster  size *) (* TO DO! Make sure + and 0,1 gets transalated back to the right constants*)
(* Issue! These constants are polymorphic! fix fix fix... *)
(*ML{* @{term "nonEmpty ys \<and> true ==> flat_tree x = []"} *} *)

(*

hipster last rev mirror flat_tree rigthmost leftmost
lemma lemma_af [thy_expl]: "last (xs2 @ xs2) = last xs2"
by (tactic {* Hipster_Tacs.induct_simp_metis @{context} @{thms List.last.simps List.rev.simps TreeDemo.mirror.simps TreeDemo.flat_tree.simps TreeDemo.rigthmost.simps TreeDemo.leftmost.simps thy_expl} *})

lemma unknown [thy_expl]: "last (flat_tree x) = rigthmost x"
oops

(* setup{* 
Tactic_Data.set_induct_simp;
*}
*)

*)
end

