theory sort_TSortPermutes'
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype 'a Tree = TNode "'a Tree" "'a" "'a Tree" | TNil

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

fun flatten :: "'a Tree => 'a list => 'a list" where
"flatten (TNode p z q) y = flatten p (Cons2 z (flatten q y))"
| "flatten (TNil) y = y"

fun elem :: "int => int list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

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

(*hipster or2
          null
          flatten
          elem
          dot
          delete
          and2
          isPermutation
          add
          toTree
          tsort *)

theorem x0 :
  "!! (x :: int list) . isPermutation (tsort x) x"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
