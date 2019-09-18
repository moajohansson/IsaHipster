theory DemoITPFull
imports "$HIPSTER_HOME/IsaHipster"
begin

(* Normal list datatype *)
datatype 'a Lst = 
   Nil
  | Cons "'a" "'a Lst" (infix ";" 65)

(* The append function. Syntactic sugar: we use +++ instead of Haskell's ++ *)
fun app :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst" (infix "+++" 60)
where 
  "Nil +++ xs = xs"
| "(x;xs) +++ ys = x;(xs +++ ys)"

(* The reverse function *)
fun rev :: "'a Lst \<Rightarrow> 'a Lst"
where 
  "rev Nil = Nil"
| "rev (x;xs) = (rev xs) +++ (x;Nil)"

(* Datatype for binary trees from your exercises *)
datatype 'a Tree = 
  Empty  
  | Node "'a" "'a Tree" "'a Tree"

(* The swap function: swaps the left and right subtree. *)
fun swap :: "'a Tree => 'a Tree"
where
  "swap Empty = Empty"
| "swap (Node data l r) = Node data (swap r) (swap l)"

(* The flatten function: turn a tree into a list *)
fun flatten :: "'a Tree \<Rightarrow> 'a Lst"
where
  "flatten Empty = Nil"
| "flatten (Node data l r) =  ((flatten l) +++ (data;Nil)) +++ (flatten r)"

hipster app rev
lemma lemma_a [thy_expl]: "y +++ Lst.Nil = y"
  apply (induct y)
  apply simp
  apply simp
  done
    
lemma lemma_aa [thy_expl]: "(y +++ z) +++ x2 = y +++ (z +++ x2)"
  apply (induct y arbitrary: x2 z)
  apply simp
  apply simp
  done

lemma lemma_ab [thy_expl]: "DemoITPFull.rev z +++ DemoITPFull.rev y = DemoITPFull.rev (y +++ z)"
  apply (induct y arbitrary: z)
  apply simp
  apply (simp add: DemoITPFull.lemma_a)
  apply simp
  apply (metis lemma_aa)
  done
  
lemma lemma_ac [thy_expl]: "DemoITPFull.rev (DemoITPFull.rev y) = y"
  apply (induct y)
  apply simp
  apply simp
  apply (metis DemoITPFull.lemma_ab DemoITPFull.rev.simps(1) DemoITPFull.rev.simps(2) Lst.distinct(1) app.elims app.simps(2))
  done

hipster swap flatten
lemma lemma_ad [thy_expl]: "swap (swap y) = y"
  apply (induct y)
  apply simp
  apply simp
  done



(* Last week's exercise 10 *)
theorem exercise10: "flatten (swap p) = rev (flatten p)"
  apply (induct p)
  apply simp
  apply simp
  apply (metis DemoITPFull.rev.simps(1) DemoITPFull.rev.simps(2) lemma_a lemma_aa lemma_ab)
  done
 
    
(* Hard exercise (optional) *)
fun qrev :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst"
where 
  "qrev Nil acc  = acc"
| "qrev (x;xs) acc = qrev xs (x;acc)"

hipster qrev rev
lemma lemma_ae [thy_expl]: "qrev (qrev z y) Lst.Nil = qrev y z"
  apply (induct z arbitrary: y)
  apply simp
  apply simp
  done
    
lemma lemma_af [thy_expl]: "DemoITPFull.rev y +++ z = qrev y z"
  apply (induct y arbitrary: z)
  apply simp
  apply simp
  apply (metis DemoITPFull.rev.simps(2) app.simps(1) lemma_aa lemma_ab lemma_ac)
  done

theorem hardExercise: "rev xs = qrev xs Nil"
sledgehammer
  by (metis lemma_a lemma_af)




(* The spine function: turns a list into a tree. *)
(* fun spine :: "'a Lst \<Rightarrow> 'a Tree"
where
  "spine Nil = Empty"
| "spine (x;xs) = Node x Empty (spine xs)"

hipster spine flatten
lemma lemma_af [thy_expl]: "flatten (spine y) = y"
  apply (induct y)
  by simp_all
*)


end