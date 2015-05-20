theory sort_SSortPermutes
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

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

fun count :: "int => int list => Nat" where
"count x (Nil2) = Z"
| "count x (Cons2 z xs) =
     (if x = z then S (count x xs) else count x xs)"

(*hipster ssortminimum delete ssort count *)

theorem x0 :
  "!! (x :: int) (y :: int list) . (count x (ssort y)) = (count x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
