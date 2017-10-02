(* From Isabelle exercsises http://isabelle.in.tum.de/exercises/ *)
theory TreeTraversal
imports "$HIPSTER_HOME/IsaHipster"

begin


datatype 'a Tree = 
  Tip 'a 
  | Node 'a  "'a Tree" "'a Tree"

fun preOrder :: "'a Tree \<Rightarrow> 'a list" where
  "preOrder (Tip a)      = [a]"
| "preOrder (Node a l r) = a#((preOrder l)@(preOrder r))"

fun postOrder :: "'a Tree  \<Rightarrow>  'a list" where
  "postOrder (Tip a)      = [a]"
| "postOrder (Node a l r) = (postOrder l)@(postOrder r)@[a]"

fun inOrder :: "'a Tree  \<Rightarrow> 'a list" where
  "inOrder (Tip a)      = [a]"
| "inOrder (Node a l r) = (inOrder l)@[a]@(inOrder r)"

fun mirror :: "'a Tree => 'a Tree"
where
  "mirror (Tip x) = Tip x"
| "mirror (Node a l r) = Node a (mirror r) (mirror l)"

hipster mirror rev preOrder postOrder inOrder
lemma lemma_a [thy_expl]: "mirror (mirror y) = y"
  apply (induct y)
  apply simp
  apply simp
  done
    
lemma lemma_aa [thy_expl]: "rev (inOrder y) = inOrder (mirror y)"
  apply (induct y)
  apply simp
  apply simp
  done
    
lemma lemma_ab [thy_expl]: "rev (postOrder y) = preOrder (mirror y)"
  apply (induct y)
  apply simp
  apply simp
  done

fun root :: "'a Tree \<Rightarrow> 'a" where
  "root (Tip a)      = a"
| "root (Node f x y) = f"

fun leftmost :: "'a Tree \<Rightarrow> 'a" where
  "leftmost (Tip a)      = a"
| "leftmost (Node f x y) = (leftmost x)"

fun rightmost :: "'a Tree \<Rightarrow> 'a" where
  "rightmost (Tip a)      = a"
| "rightmost (Node f x y) = (rightmost y)"

  setup Tactic_Data.set_induct_sledgehammer 
hipster root hd last leftmost rightmost inOrder
lemma lemma_ac [thy_expl]: "last (inOrder y) = rightmost y"
  apply (induct y)
  apply simp
  apply simp
  apply (metis append_is_Nil_conv inOrder.simps(1) inOrder.simps(2) rightmost.elims snoc_eq_iff_butlast)
  done
    
lemma lemma_ad [thy_expl]: "hd (inOrder z @ y) = leftmost z"
  apply (induct z arbitrary: y)
  apply simp
  apply simp
  done
    
lemma lemma_ae [thy_expl]: "last (y @ inOrder z) = rightmost z"
  apply (induct y arbitrary: z)
  apply simp
  apply (simp add: TreeTraversal.lemma_ac)
  apply simp
  apply (metis append_is_Nil_conv inOrder.simps(1) inOrder.simps(2) list.simps(3) rightmost.elims)
  done
(*   

(* 
With this tactic, we don't use Sledgehammer in the "Easy tactic", so we get more results.
*) 
setup Tactic_Data.set_sledge_induct_sledge
hipster root hd last leftmost rightmost inOrder

 
lemma lemma_ac [thy_expl]: "hd (inOrder y) = leftmost y"
  apply (induct y)
apply simp
apply simp
apply (metis append_is_Nil_conv hd_append2 inOrder.simps(1) inOrder.simps(2) leftmost.elims self_append_conv2 snoc_eq_iff_butlast)
done

lemma lemma_ad [thy_expl]: "last (inOrder y) = rightmost y"
apply (induct y)
  apply simp
  apply simp
apply (metis append_is_Nil_conv inOrder.simps(1) inOrder.simps(2) rightmost.elims snoc_eq_iff_butlast)
done

lemma lemma_ae [thy_expl]: "hd (inOrder z @ y) = leftmost z"
apply (metis (no_types, lifting) TreeTraversal.lemma_ac append_is_Nil_conv hd_append2 inOrder.simps(1) inOrder.simps(2) leftmost.elims snoc_eq_iff_butlast)
done

lemma lemma_af [thy_expl]: "last (y @ inOrder z) = rightmost z"
apply (induct y arbitrary: z)
apply simp
apply (simp add: lemma_ad)
apply simp
apply (metis append_is_Nil_conv inOrder.simps(1) inOrder.simps(2) list.simps(3) rightmost.elims)
done 
*)


