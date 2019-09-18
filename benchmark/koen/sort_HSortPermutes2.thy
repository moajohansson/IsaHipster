theory sort_HSortPermutes'
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Heap = Node "'a Heap" "'a" "'a Heap" | Nil2

fun toHeap2 :: "int list => (int Heap) list" where
"toHeap2 (Nil2) = Nil2"
| "toHeap2 (Cons2 y z) = Cons2 (Node (Nil2) y (Nil2)) (toHeap2 z)"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

fun hmerge :: "int Heap => int Heap => int Heap" where
"hmerge (Node z x2 x3) (Node x4 x5 x6) =
   (if x2 <= x5 then Node (hmerge x3 (Node x4 x5 x6)) x2 z else
      Node (hmerge (Node z x2 x3) x6) x5 x4)"
| "hmerge (Node z x2 x3) (Nil2) = Node z x2 x3"
| "hmerge (Nil2) y = y"

fun hpairwise :: "(int Heap) list => (int Heap) list" where
"hpairwise (Nil2) = Nil2"
| "hpairwise (Cons2 p (Nil2)) = Cons2 p (Nil2)"
| "hpairwise (Cons2 p (Cons2 q qs)) =
     Cons2 (hmerge p q) (hpairwise qs)"

fun hmerging :: "(int Heap) list => int Heap" where
"hmerging (Nil2) = Nil2"
| "hmerging (Cons2 p (Nil2)) = p"
| "hmerging (Cons2 p (Cons2 z x2)) =
     hmerging (hpairwise (Cons2 p (Cons2 z x2)))"

fun toHeap :: "int list => int Heap" where
"toHeap x = hmerging (toHeap2 x)"

fun toList :: "int Heap => int list" where
"toList (Node p y q) = Cons2 y (toList (hmerge p q))"
| "toList (Nil2) = Nil2"

fun elem :: "int => int list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun hsort :: "int list => int list" where
"hsort x =
   dot
     (% (y :: int Heap) => toList y) (% (z :: int list) => toHeap z) x"

fun delete :: "int => int list => int list" where
"delete x (Nil2) = Nil2"
| "delete x (Cons2 z ys) =
     (if x = z then ys else Cons2 z (delete x ys))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "int list => int list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

(*hipster toHeap2
          or2
          null
          hmerge
          hpairwise
          hmerging
          toHeap
          toList
          elem
          dot
          hsort
          delete
          and2
          isPermutation *)

theorem x0 :
  "!! (x :: int list) . isPermutation (hsort x) x"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
