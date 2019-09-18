theory list_concat_fmap_bind
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun fmap :: "('a => 'b) => 'a list => 'b list" where
"fmap x (Nil2) = Nil2"
| "fmap x (Cons2 z xs) = Cons2 (x z) (fmap x xs)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun bind :: "'a list => ('a => 'b list) => 'b list" where
"bind (Nil2) y = Nil2"
| "bind (Cons2 z xs) y = append (y z) (bind xs y)"

fun concat2 :: "('a list) list => 'a list" where
"concat2 (Nil2) = Nil2"
| "concat2 (Cons2 xs xss) = append xs (concat2 xss)"

(*hipster fmap append bind concat2 *)

hipster fmap append bind concat2

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes fmap.simps append.simps bind.simps concat2.simps)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes fmap.simps append.simps bind.simps concat2.simps)

lemma lemma_ab [thy_expl]: "append (fmap x2 y2) (fmap x2 z2) = fmap x2 (append y2 z2)"
by (hipster_induct_schemes fmap.simps append.simps bind.simps concat2.simps)

lemma lemma_ac [thy_expl]: "append (bind x1 y1) (bind z1 y1) = bind (append x1 z1) y1"
by (hipster_induct_schemes fmap.simps append.simps bind.simps concat2.simps)

theorem x0 :
  "!! (f :: ('a => 'b list)) (xs :: 'a list) .
     (concat2 (fmap f xs)) = (bind xs f)"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
