theory heap_SortSorts
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Heap = Node "Heap" "Nat" "Heap" | Nil2

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun merge :: "Heap => Heap => Heap" where
"merge (Node z x2 x3) (Node x4 x5 x6) =
   (if le x2 x5 then Node (merge x3 (Node x4 x5 x6)) x2 z else
      Node (merge (Node z x2 x3) x6) x5 x4)"
| "merge (Node z x2 x3) (Nil2) = Node z x2 x3"
| "merge (Nil2) y = y"

fun toList :: "Nat => Heap => Nat list" where
"toList (Z) y = Nil2"
| "toList (S z) (Node x2 x3 x4) =
     Cons2 x3 (toList z (merge x2 x4))"
| "toList (S z) (Nil2) = Nil2"

fun insert2 :: "Nat => Heap => Heap" where
"insert2 x y = merge (Node Nil2 x Nil2) y"

fun toHeap :: "Nat list => Heap" where
"toHeap (Nil2) = Nil2"
| "toHeap (Cons2 y xs) = insert2 y (toHeap xs)"

fun heapSize :: "Heap => Nat" where
"heapSize (Node l y r) = S (plus (heapSize l) (heapSize r))"
| "heapSize (Nil2) = Z"

fun toList2 :: "Heap => Nat list" where
"toList2 x = toList (heapSize x) x"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun hsort :: "Nat list => Nat list" where
"hsort x =
   dot (% (y :: Heap) => toList2 y) (% (z :: Nat list) => toHeap z) x"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "Nat list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (le y y2) (ordered (Cons2 y2 xs))"

(*hipster plus
          le
          merge
          toList
          insert2
          toHeap
          heapSize
          toList2
          dot
          hsort
          and2
          ordered *)

theorem x0 :
  "!! (x :: Nat list) . ordered (hsort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
