theory list_assoc
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun bind :: "'a list => ('a => 'b list) => 'b list" where
"bind (Nil2) y = Nil2"
| "bind (Cons2 z xs) y = append (y z) (bind xs y)"

(*hipster append bind *)

hipster append bind
lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes append.simps bind.simps)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes append.simps bind.simps)

lemma lemma_ab [thy_expl]: "append (bind x1 y1) (bind z1 y1) = bind (append x1 z1) y1"
by (hipster_induct_schemes append.simps bind.simps)

theorem x0 :
  "!! (m :: 'a list) (f :: ('a => 'b list)) (g :: ('b => 'c list)) .
     (bind (bind m f) g) = (bind m (% (x :: 'a) => bind (f x) g))"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
