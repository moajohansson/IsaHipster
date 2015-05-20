theory sort_QSortSorts
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun filter :: "('t => bool) => 't list => 't list" where
"filter p (Nil2) = Nil2"
| "filter p (Cons2 y z) =
     (if p y then Cons2 y (filter p z) else filter p z)"

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

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

(*hipster filter append qsort and2 ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (qsort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
