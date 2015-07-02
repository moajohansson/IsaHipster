theory sort_MSortBUIsSort
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun map2 :: "('t2 => 't) => 't2 list => 't list" where
"map2 f (Nil2) = Nil2"
| "map2 f (Cons2 y z) = Cons2 (f y) (map2 f z)"

fun lmerge :: "int list => int list => int list" where
"lmerge (Nil2) y = y"
| "lmerge (Cons2 z x2) (Nil2) = Cons2 z x2"
| "lmerge (Cons2 z x2) (Cons2 x3 x4) =
     (if z <= x3 then Cons2 z (lmerge x2 (Cons2 x3 x4)) else
        Cons2 x3 (lmerge (Cons2 z x2) x4))"

fun pairwise :: "(int list) list => (int list) list" where
"pairwise (Nil2) = Nil2"
| "pairwise (Cons2 xs (Nil2)) = Cons2 xs (Nil2)"
| "pairwise (Cons2 xs (Cons2 ys xss)) =
     Cons2 (lmerge xs ys) (pairwise xss)"

fun mergingbu :: "(int list) list => int list" where
"mergingbu (Nil2) = Nil2"
| "mergingbu (Cons2 xs (Nil2)) = xs"
| "mergingbu (Cons2 xs (Cons2 z x2)) =
     mergingbu (pairwise (Cons2 xs (Cons2 z x2)))"

fun insert2 :: "int => int list => int list" where
"insert2 x (Nil2) = Cons2 x (Nil2)"
| "insert2 x (Cons2 z xs) =
     (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"

fun isort :: "int list => int list" where
"isort (Nil2) = Nil2"
| "isort (Cons2 y xs) = insert2 y (isort xs)"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun msortbu :: "int list => int list" where
"msortbu x =
   dot
     (% (y :: (int list) list) => mergingbu y)
     (% (z :: int list) => map2 (% (x2 :: int) => Cons2 x2 (Nil2)) z) x"

(*hipster map2
          lmerge
          pairwise
          mergingbu
          insert2
          isort
          dot
          msortbu *)

theorem x0 :
  "!! (x :: int list) . (msortbu x) = (isort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
