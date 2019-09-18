theory tree_sort_SortPermutes
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2

datatype Nat = Z | S "Nat"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun flatten :: "'a Tree => 'a list => 'a list" where
"flatten (Node q z q2) y = flatten q (Cons2 z (flatten q2 y))"
| "flatten (Nil2) y = y"

fun equal2 :: "Nat => Nat => bool" where
"equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

fun count :: "Nat => Nat list => Nat" where
"count x (Nil2) = Z"
| "count x (Cons2 z xs) =
     (if equal2 x z then S (count x xs) else count x xs)"

fun add :: "Nat => Nat Tree => Nat Tree" where
"add x (Node q z q2) =
   (if le x z then Node (add x q) z q2 else Node q z (add x q2))"
| "add x (Nil2) = Node (Nil2) x (Nil2)"

fun toTree :: "Nat list => Nat Tree" where
"toTree (Nil2) = Nil2"
| "toTree (Cons2 y xs) = add y (toTree xs)"

fun tsort :: "Nat list => Nat list" where
"tsort x = flatten (toTree x) (Nil2)"

(*hipster le flatten equal2 count add toTree tsort *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat list) . (count x (tsort y)) = (count x y)"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
