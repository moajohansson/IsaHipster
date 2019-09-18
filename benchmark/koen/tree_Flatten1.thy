theory tree_Flatten1
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2

fun flatten1 :: "('a Tree) list => 'a list" where
"flatten1 (Nil2) = Nil2"
| "flatten1 (Cons2 (Node (Node x3 x4 x5) x2 q) ps) =
     flatten1 (Cons2 (Node x3 x4 x5) (Cons2 (Node (Nil2) x2 q) ps))"
| "flatten1 (Cons2 (Node (Nil2) x2 q) ps) =
     Cons2 x2 (flatten1 (Cons2 q ps))"
| "flatten1 (Cons2 (Nil2) ps) = flatten1 ps"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun flatten0 :: "'a Tree => 'a list" where
"flatten0 (Node p y q) =
   append (append (flatten0 p) (Cons2 y (Nil2))) (flatten0 q)"
| "flatten0 (Nil2) = Nil2"

(*hipster flatten1 append flatten0 *)

theorem x0 :
  "!! (p :: 'a Tree) . (flatten1 (Cons2 p (Nil2))) = (flatten0 p)"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
