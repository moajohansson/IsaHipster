theory list_weird_concat_fmap_bind
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

function weirdconcat :: "('a list) list => 'a list" where
"weirdconcat (Nil2) = Nil2"
| "weirdconcat (Cons2 (Nil2) xss) = weirdconcat xss"
| "weirdconcat (Cons2 (Cons2 z xs) xss) =
     Cons2 z (weirdconcat (Cons2 xs xss))"
by pat_completeness auto

fun fmap :: "('a => 'b) => 'a list => 'b list" where
"fmap x (Nil2) = Nil2"
| "fmap x (Cons2 z xs) = Cons2 (x z) (fmap x xs)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun bind :: "'a list => ('a => 'b list) => 'b list" where
"bind (Nil2) y = Nil2"
| "bind (Cons2 z xs) y = append (y z) (bind xs y)"

(*hipster weirdconcat fmap append bind *)

(*hipster append bind *)

(*hipster append bind fmap*)

lemma lemma_a [thy_expl]: "append x2 Nil2 = x2"
by (hipster_induct_schemes fmap.simps append.simps bind.simps)

lemma lemma_aa [thy_expl]: "append (append x1 y1) z1 = append x1 (append y1 z1)"
by (hipster_induct_schemes fmap.simps append.simps bind.simps)

lemma lemma_ab [thy_expl]: "append (fmap x2 y2) (fmap x2 z2) = fmap x2 (append y2 z2)"
by (hipster_induct_schemes fmap.simps append.simps bind.simps)

lemma lemma_ac [thy_expl]: "append (bind x1 y1) (bind z1 y1) = bind (append x1 z1) y1"
by (hipster_induct_schemes fmap.simps append.simps bind.simps)

(*hipster weirdconcat append bind fmap \<Longrightarrow> No code equations for weirdconcat *)
thm weirdconcat.psimps



theorem x0 :
  "!! (f :: ('a => 'b list)) (xs :: 'a list) .
     (weirdconcat (fmap f xs)) = (bind xs f)"
(*proof -
fix f xs
show "(weirdconcat (fmap f xs)) = (bind xs f)"
     apply(induction xs f rule: bind.induct)
     apply(simp_all add: weirdconcat.psimps)
     sledgehammer*)
     (*apply(metis (full_types) thy_expl weirdconcat.psimps fmap.simps bind.simps)*)
(*by (hipster_induct_schemes fmap.simps append.simps bind.simps list.exhaust weirdconcat.psimps)   Unification loop! *)

  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
