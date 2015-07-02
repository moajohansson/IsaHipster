theory sort_TSortSorts
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = TNode "'a Tree" "'a" "'a Tree" | TNil

fun flatten :: "'a Tree => 'a list => 'a list" where
"flatten (TNode p z q) y = flatten p (Cons2 z (flatten q y))"
| "flatten (TNil) y = y"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

fun add :: "int => int Tree => int Tree" where
"add x (TNode p z q) =
   (if x <= z then TNode (add x p) z q else TNode p z (add x q))"
| "add x (TNil) = TNode (TNil) x (TNil)"

fun toTree :: "int list => int Tree" where
"toTree (Nil2) = TNil"
| "toTree (Cons2 y xs) = add y (toTree xs)"

fun tsort :: "int list => int list" where
"tsort x =
   dot
     (% (y :: (int list => int list)) => y (Nil2))
     (% (z :: int list) =>
        dot
          (% (x2 :: int Tree) => % (x3 :: int list) => flatten x2 x3)
          (% (x4 :: int list) => toTree x4) z)
     x"

(*hipster flatten dot and2 ordered add toTree tsort *)

theorem x0 :
  "!! (x :: int list) . ordered (tsort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
