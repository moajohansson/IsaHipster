theory DemoITP
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


(* Last week's exercise 10 *)
theorem exercise10: "flatten (swap p) = rev (flatten p)"
  apply hipster_induct
 
  


    
    
    
    

    
    
(* A tail recursive reverse function *)
fun qrev :: "'a Lst \<Rightarrow> 'a Lst \<Rightarrow> 'a Lst"
where 
  "qrev Nil acc  = acc"
| "qrev (x;xs) acc = qrev xs (x;acc)"
  
(* Hard exercise (optional) *)
theorem hardExercise: "rev xs = qrev xs Nil"





  
  
  
  
  
  
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