theory list_PairEvens
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

datatype Nat = Z | S "Nat"

fun pairs :: "'t list => (('t, 't) Pair2) list" where
"pairs (Nil2) = Nil2"
| "pairs (Cons2 y (Nil2)) = Nil2"
| "pairs (Cons2 y (Cons2 y2 xs)) = Cons2 (Pair y y2) (pairs xs)"

fun map2 :: "('t2 => 't) => 't2 list => 't list" where
"map2 f (Nil2) = Nil2"
| "map2 f (Cons2 y z) = Cons2 (f y) (map2 f z)"

fun length :: "'t list => Nat" where
"length (Nil2) = Z"
| "length (Cons2 y xs) = S (length xs)"

fun fst :: "('a, 'b) Pair2 => 'a" where
"fst (Pair y z) = y"

function evens :: "'a list => 'a list"
         and odds :: "'a list => 'a list" where
"evens (Nil2) = Nil2"
| "evens (Cons2 y xs) = Cons2 y (odds xs)"
| "odds (Nil2) = Nil2"
| "odds (Cons2 y xs) = evens xs"
by pat_completeness auto

fun even :: "Nat => bool" where
"even (Z) = True"
| "even (S (Z)) = False"
| "even (S (S z)) = even z"

(*hipster pairs map2 length fst evens odds even *)

theorem x0 :
  "!! (xs :: 'b list) .
     (even (length xs)) ==>
       ((map2 (% (x :: ('b, 'b) Pair2) => fst x) (pairs xs)) =
          (evens xs))"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
