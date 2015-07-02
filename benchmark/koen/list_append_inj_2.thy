theory list_append_inj_2
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

(*hipster append *)

theorem x0 :
  "!! (xs :: 'a list) (ys :: 'a list) (zs :: 'a list) .
     ((append xs ys) = (append xs zs)) ==> (ys = zs)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
