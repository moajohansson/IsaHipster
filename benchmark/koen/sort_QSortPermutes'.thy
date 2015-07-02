theory sort_QSortPermutes'
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

fun filter :: "('t => bool) => 't list => 't list" where
"filter p (Nil2) = Nil2"
| "filter p (Cons2 y z) =
     (if p y then Cons2 y (filter p z) else filter p z)"

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

fun qsort :: "int list => int list" where
"qsort (Nil2) = Nil2"
| "qsort (Cons2 y xs) =
     append
       (append
          (qsort (filter (% (z :: int) => z <= y) xs)) (Cons2 y (Nil2)))
       (qsort (filter (% (x2 :: int) => x2 > y) xs))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "int list => int list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

(*hipster or2
          null
          filter
          elem
          delete
          append
          qsort
          and2
          isPermutation *)

theorem x0 :
  "!! (x :: int list) . isPermutation (qsort x) x"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
