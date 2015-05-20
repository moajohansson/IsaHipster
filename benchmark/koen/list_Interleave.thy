theory list_Interleave
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun interleave :: "'a list => 'a list => 'a list" where
"interleave (Nil2) y = y"
| "interleave (Cons2 z xs) y = Cons2 z (interleave y xs)"

function evens :: "'a list => 'a list"
         and odds :: "'a list => 'a list" where
"evens (Nil2) = Nil2"
| "evens (Cons2 y xs) = Cons2 y (odds xs)"
| "odds (Nil2) = Nil2"
| "odds (Cons2 y xs) = evens xs"
by pat_completeness auto

(*hipster interleave evens odds *)

theorem x0 :
  "!! (xs :: 'a list) . (interleave (evens xs) (odds xs)) = xs"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
