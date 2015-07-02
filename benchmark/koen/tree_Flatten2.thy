theory tree_Flatten2
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = Node "'a Tree" "'a" "'a Tree" | Nil2

fun flatten2 :: "'a Tree => 'a list => 'a list" where
"flatten2 (Node p z q) y = flatten2 p (Cons2 z (flatten2 q y))"
| "flatten2 (Nil2) y = y"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun flatten0 :: "'a Tree => 'a list" where
"flatten0 (Node p y q) =
   append (append (flatten0 p) (Cons2 y (Nil2))) (flatten0 q)"
| "flatten0 (Nil2) = Nil2"

(*hipster flatten2 append flatten0 *)

theorem x0 :
  "!! (p :: 'a Tree) . (flatten2 p (Nil2)) = (flatten0 p)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
