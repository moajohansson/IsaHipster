theory TreeDemo
imports "$HIPSTER_HOME/IsaHipster"

begin
setup Misc_Data.set_noisy
(* setup Tactic_Data.set_induct_simp *)
setup Tactic_Data.set_sledge_induct_sledge

datatype 'a Tree = 
  Leaf 'a 
  | Node "'a Tree" 'a "'a Tree"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Leaf x) = Leaf x"
| "mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun tmap :: "('a => 'b) => 'a Tree => 'b Tree"
where
  "tmap f (Leaf x) = Leaf (f x)"
| "tmap f (Node l x r) = Node (tmap f l) (f x) (tmap f r)" 


(* First call to Hipster: Explore tmap and mirror *)
 hipster tmap mirror
lemma lemma_a [thy_expl]: "mirror (mirror y) = y"
  apply (induct y)
  by simp_all
    
lemma lemma_aa [thy_expl]: "mirror (tmap y z) = tmap y (mirror z)"
  apply (induct z)
  by simp_all


fun flat_tree :: "'a Tree => 'a list"
where
  "flat_tree (Leaf x) = [x]"
| "flat_tree (Node l x r) = (flat_tree l) @ [x] @ (flat_tree r)"

(* Second call to Hipster: Explore relation to lists: flat_tree tmap mirror rev map *)
hipster flat_tree tmap mirror rev map
lemma lemma_ab [thy_expl]: "rev (flat_tree y) = flat_tree (mirror y)"
  apply (induct y)
  by simp_all
    
lemma lemma_ac [thy_expl]: "flat_tree (tmap y z) = map y (flat_tree z)"
  apply (induct z)
  by simp_all



fun rightmost :: "'a Tree \<Rightarrow> 'a"
where 
  "rightmost (Leaf x) = x"
| "rightmost (Node l x r) = rightmost r"

fun leftmost :: "'a Tree \<Rightarrow> 'a"
where 
  "leftmost (Leaf x) = x"
| "leftmost (Node l x r) = leftmost l"

(* Explore leftmost rightmost mirror tmap *)
hipster leftmost rightmost mirror tmap
lemma lemma_ad [thy_expl]: "leftmost (mirror y) = rightmost y"
  apply (induct y)
  apply simp
apply simp
  done
    
lemma lemma_ae [thy_expl]: "rightmost (mirror y) = leftmost y"
apply (metis lemma_a lemma_ad)
done

lemma lemma_af [thy_expl]: "leftmost (tmap z x2) = z (leftmost x2)"
apply (induct x2)
apply simp
apply simp
done

lemma lemma_ag [thy_expl]: "rightmost (tmap z x2) = z (rightmost x2)"
apply (metis TreeDemo.lemma_ad lemma_aa lemma_af)
done



(*
setup Tactic_Data.set_induct_simp
(* If we just use induction and simp, we fail to prove the second one, as lemma_af isn't in the simpset *) 
hipster hd mirror flat_tree rightmost leftmost    

lemma lemma_af [thy_expl]: "hd (flat_tree z @ y) = leftmost z"
  apply (induct z arbitrary: y)
  by simp_all
    
lemma unknown [thy_expl]: "hd (flat_tree y) = leftmost y"
  oops
*)    

(* Third call to Hipster: hd mirror flat_tree  rightmost leftmost*)
hipster hd flat_tree rightmost leftmost
lemma lemma_af [thy_expl]: "hd (flat_tree z @ y) = leftmost z"
  apply (induct z arbitrary: y)
  by simp_all
    
lemma lemma_ag [thy_expl]: "hd (flat_tree y) = leftmost y"
  by (metis TreeDemo.lemma_af flat_tree.simps(1) flat_tree.simps(2) leftmost.elims list.sel(1))    

(*lemma lemma_af [thy_expl]: "hd (flat_tree y) = leftmost y"
  apply (induct y)
  apply simp_all
  by (metis (no_types, lifting) append_is_Nil_conv flat_tree.simps(1) flat_tree.simps(2) hd_append2 leftmost.elims snoc_eq_iff_butlast)
    
lemma lemma_ag [thy_expl]: "hd (flat_tree z @ y) = leftmost z"
  apply (induct z arbitrary: y)
  by simp_all
*)

hipster last flat_tree rightmost leftmost
lemma lemma_ah [thy_expl]: "last (flat_tree y) = rightmost y"
  by (metis append_is_Nil_conv flat_tree.simps(1) flat_tree.simps(2) hd_rev lemma_ab lemma_ad lemma_af rightmost.elims snoc_eq_iff_butlast)
  
lemma lemma_ai [thy_expl]: "last (y @ flat_tree z) = rightmost z"
  by (metis hd_rev last_appendR lemma_ab lemma_ad lemma_ag lemma_ah rev_append)    
    












(* setup{* 
Tactic_Data.set_induct_simp;
*}
*)

end

