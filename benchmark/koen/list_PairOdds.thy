theory list_PairOdds
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

fun snd :: "('a, 'b) Pair2 => 'b" where
"snd (Pair y z) = z"

fun pairs :: "'t list => (('t, 't) Pair2) list" where
"pairs (Nil2) = Nil2"
| "pairs (Cons2 y (Nil2)) = Nil2"
| "pairs (Cons2 y (Cons2 y2 xs)) = Cons2 (Pair y y2) (pairs xs)"

fun map2 :: "('t2 => 't) => 't2 list => 't list" where
"map2 f (Nil2) = Nil2"
| "map2 f (Cons2 y z) = Cons2 (f y) (map2 f z)"

function evens :: "'a list => 'a list"
         and odds :: "'a list => 'a list" where
"evens (Nil2) = Nil2"
| "evens (Cons2 y xs) = Cons2 y (odds xs)"
| "odds (Nil2) = Nil2"
| "odds (Cons2 y xs) = evens xs"
by pat_completeness auto

(*hipster snd pairs map2 evens odds *)

theorem x0 :
  "
     (map2 (% (x :: ('t, 't) Pair2) => snd x) (pairs xs)) = (odds xs)"
     apply(induction xs rule: evens_odds.pinduct)
     apply(simp_all add:odds.psimps evens.psimps evens.pelims odds.pelims)
     
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
