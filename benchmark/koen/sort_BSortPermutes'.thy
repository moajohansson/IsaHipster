theory sort_BSortPermutes'
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun sort2 :: "int => int => int list" where
"sort2 x y =
   (if x <= y then Cons2 x (Cons2 y (Nil2)) else
      Cons2 y (Cons2 x (Nil2)))"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

function evens :: "'a list => 'a list"
         and odds :: "'a list => 'a list" where
"evens (Nil2) = Nil2"
| "evens (Cons2 y xs) = Cons2 y (odds xs)"
| "odds (Nil2) = Nil2"
| "odds (Cons2 y xs) = evens xs"
by pat_completeness auto

fun elem :: "int => int list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"

fun delete :: "int => int list => int list" where
"delete x (Nil2) = Nil2"
| "delete x (Cons2 z ys) =
     (if x = z then ys else Cons2 z (delete x ys))"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun pairs :: "int list => int list => int list" where
"pairs (Nil2) y = y"
| "pairs (Cons2 z x2) (Nil2) = Cons2 z x2"
| "pairs (Cons2 z x2) (Cons2 x3 x4) =
     append (sort2 z x3) (pairs x2 x4)"

fun stitch :: "int list => int list => int list" where
"stitch (Nil2) y = y"
| "stitch (Cons2 z xs) y = Cons2 z (pairs xs y)"

fun bmerge :: "int list => int list => int list" where
"bmerge (Nil2) y = Nil2"
| "bmerge (Cons2 z x2) (Nil2) = Cons2 z x2"
| "bmerge (Cons2 z (Nil2)) (Cons2 x3 (Nil2)) = sort2 z x3"
| "bmerge (Cons2 z (Nil2)) (Cons2 x3 (Cons2 x5 x6)) =
     stitch
       (bmerge (evens (Cons2 z (Nil2))) (evens (Cons2 x3 (Cons2 x5 x6))))
       (bmerge (odds (Cons2 z (Nil2))) (odds (Cons2 x3 (Cons2 x5 x6))))"
| "bmerge (Cons2 z (Cons2 x7 x8)) (Cons2 x3 x4) =
     stitch
       (bmerge (evens (Cons2 z (Cons2 x7 x8))) (evens (Cons2 x3 x4)))
       (bmerge (odds (Cons2 z (Cons2 x7 x8))) (odds (Cons2 x3 x4)))"

fun bsort :: "int list => int list" where
"bsort (Nil2) = Nil2"
| "bsort (Cons2 y (Nil2)) = Cons2 y (Nil2)"
| "bsort (Cons2 y (Cons2 x2 x3)) =
     bmerge
       (bsort (evens (Cons2 y (Cons2 x2 x3))))
       (bsort (odds (Cons2 y (Cons2 x2 x3))))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "int list => int list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

(*hipster sort2
          or2
          null
          evens
          odds
          elem
          delete
          append
          pairs
          stitch
          bmerge
          bsort
          and2
          isPermutation *)

theorem x0 :
  "!! (x :: int list) . isPermutation (bsort x) x"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
