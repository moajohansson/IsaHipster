theory DemoFacit
imports "$HIPSTER_HOME/IsaHipster"

begin

(* Normal list datatype *)
datatype 'a Lst = 
   Nil
  | Cons "'a" "'a Lst" (infix ";" 65)

(* The append function. We must use +++ instead of Haskell's ++ *)
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
apply (induction y)
apply simp
by simp

lemma lemma_aa [thy_expl]: "(y +++ z) +++ x2 = y +++ (z +++ x2)"
apply (induction y)
apply simp
by simp

lemma lemma_ab [thy_expl]: "Demo.rev z +++ Demo.rev y = Demo.rev (y +++ z)"
apply (induction y)
apply simp
apply (metis Demo.lemma_a)
apply simp
by (metis lemma_aa)

lemma lemma_ac [thy_expl]: "Demo.rev (Demo.rev y) = y"
apply (induction y)
apply simp
apply simp
by (metis Demo.lemma_a Demo.rev.simps(1) Demo.rev.simps(2) Lst.distinct(1) app.elims app.simps(2) lemma_ab)

(* Last week's exercise 10 *)
theorem exercise10: "flatten (swap p) = rev (flatten p)"
apply (induction p)
apply simp
apply simp
by (metis Demo.rev.simps(1) Demo.rev.simps(2) lemma_a lemma_aa lemma_ab)






(* The spine function: turns a list into a tree. *)
fun spine :: "'a Lst \<Rightarrow> 'a Tree"
where
  "spine Nil = Empty"
| "spine (x;xs) = Node x Empty (spine xs)"

hipster spine flatten
lemma lemma_ad [thy_expl]: "(flatten z) +++ (y ; flatten x2) = flatten (Node y z x2)"
apply (induction x2)
apply simp
apply (metis lemma_a)
apply simp
by (metis app.simps(1) app.simps(2) lemma_aa)

lemma lemma_ae [thy_expl]: "flatten (spine y) = y"
apply (induction y)
apply simp
by simp
end