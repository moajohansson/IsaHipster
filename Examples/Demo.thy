theory Demo
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
by simp_all

lemma lemma_aa [thy_expl]: "(y +++ z) +++ x2 = y +++ (z +++ x2)"
apply (induct y arbitrary: x2 z)
by simp_all

lemma lemma_ab [thy_expl]: "Demo.rev z +++ Demo.rev y = Demo.rev (y +++ z)"
apply (induct y arbitrary: z)
apply (simp_all add: Demo.lemma_a)
by (metis lemma_aa)

lemma lemma_ac [thy_expl]: "Demo.rev (Demo.rev y) = y"
apply (induct y)
apply simp_all
by (metis Demo.rev.simps(1) Demo.rev.simps(2) Lst.distinct(1) app.elims app.simps(2) lemma_ab)



hipster swap flatten
lemma lemma_ad [thy_expl]: "swap (swap y) = y"
apply (induct y)
by simp_all


(* Last week's exercise 10 *)
theorem exercise10: "flatten (swap p) = rev (flatten p)"
(*  apply hipster_induct *)
  apply (induct p)
  apply simp_all
  by (metis Demo.rev.simps(1) Demo.rev.simps(2) lemma_a lemma_aa lemma_ab)

(* Hard exercise (optional) *)
fun qrev :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst"
where 
  "qrev Nil acc  = acc"
| "qrev (x;xs) acc = qrev xs (x;acc)"

hipster qrev rev
lemma lemma_ae [thy_expl]: "Demo.rev y +++ z = qrev y z"
  apply (induct y arbitrary: z)
  apply simp_all
  by (metis Demo.rev.simps(2) app.simps(1) lemma_aa lemma_ab lemma_ac)

theorem hardExercise: "rev xs = qrev xs Nil"
sledgehammer
  by (metis lemma_a lemma_ae)




(* The spine function: turns a list into a tree. *)
fun spine :: "'a Lst \<Rightarrow> 'a Tree"
where
  "spine Nil = Empty"
| "spine (x;xs) = Node x Empty (spine xs)"

hipster spine flatten
lemma lemma_af [thy_expl]: "flatten (spine y) = y"
  apply (induct y)
  by simp_all

(* Example: Histering a buggy rot function *)
fun rot :: "nat \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst"
  where
    "rot 0 xs = xs"
  | "rot (Suc n) Nil = Nil"
  | "rot (Suc n) (x;xs) = rot n (xs+++(Cons x Nil))" 
 (* | "rot (Suc n) (x;xs) = rot n xs+++(Cons x Nil)" <--- This is the buggy version*)
    
fun len :: "'a Lst \<Rightarrow> nat"  
  where
    "len Nil = 0"
  | "len (x;xs) = Suc(len xs)"

  
hipster rot len 

(* Properties discovered  for the buggy definition of rot. Note the first one, indicates that
  rotating around the length is reversing! 

lemma lemma_ag [thy_expl]: "rot (len y) y = Demo.rev y"
apply (induct y)
apply simp
apply simp
done

lemma lemma_ah [thy_expl]: "rot (Suc (len y)) y = Demo.rev y"
apply (induct y)
apply simp
apply simp
done

lemma lemma_ai [thy_expl]: "rot (len z) (z +++ y) = y +++ Demo.rev z"
apply (induct z arbitrary: y)
apply simp
apply (simp add: lemma_a)
apply simp
using lemma_aa apply blast
done

lemma lemma_aj [thy_expl]: "rot (len (z +++ y)) z = Demo.rev z"
apply (induct z arbitrary: y)
apply simp
apply (metis rot.elims rot.simps(2))
apply simp
done

*)

end