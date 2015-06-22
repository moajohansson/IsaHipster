theory sort_SSortSorts
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun ssortminimum :: "int => int list => int" where
"ssortminimum x (Nil2) = x"
| "ssortminimum x (Cons2 z ys) =
     (if z <= x then ssortminimum z ys else ssortminimum x ys)"

fun delete :: "int => int list => int list" where
"delete x (Nil2) = Nil2"
| "delete x (Cons2 z ys) =
     (if x = z then ys else Cons2 z (delete x ys))"

fun ssort :: "int list => int list" where
"ssort (Nil2) = Nil2"
| "ssort (Cons2 y ys) =
     Cons2
       (ssortminimum y ys)
       (ssort (delete (ssortminimum y ys) (Cons2 y ys)))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

(*hipster ssortminimum delete ssort and2 ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (ssort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
