theory list_return_1
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun return :: "'a => 'a list" where
"return x = Cons2 x (Nil2)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun bind :: "'a list => ('a => 'b list) => 'b list" where
"bind (Nil2) y = Nil2"
| "bind (Cons2 z xs) y = append (y z) (bind xs y)"

(*hipster return append bind *)

hipster append bind
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps bind.simps)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes append.simps bind.simps)

lemma lemma_ab [thy_expl]: "append (bind x1 y1) (bind z1 y1) = bind (append x1 z1) y1"
by (hipster_induct_schemes append.simps bind.simps)

theorem x0 :
  "!! (x :: 'a) (f :: ('a => 'b list)) . (bind (return x) f) = (f x)"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
