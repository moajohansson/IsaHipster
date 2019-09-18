theory heap_SortPermutes2
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

datatype Heap = Node "Heap" "Nat" "Heap" | Nil2

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S n) y = S (plus n y)"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'a list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

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

fun equal2 :: "Nat => Nat => bool" where
"equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

fun elem :: "Nat => Nat list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (equal2 x z) (elem x ys)"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun hsort :: "Nat list => Nat list" where
"hsort x =
   dot (% (y :: Heap) => toList2 y) (% (z :: Nat list) => toHeap z) x"

fun delete :: "Nat => Nat list => Nat list" where
"delete x (Nil2) = Nil2"
| "delete x (Cons2 z ys) =
     (if equal2 x z then ys else Cons2 z (delete x ys))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "Nat list => Nat list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

(*hipster plus
          or2
          null
          le
          merge
          toList
          insert2
          toHeap
          heapSize
          toList2
          equal2
          elem
          dot
          hsort
          delete
          and2
          isPermutation *)

theorem x0 :
  "!! (x :: Nat list) . isPermutation (hsort x) x"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
