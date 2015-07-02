theory sort_MSortBU2Sorts
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun risers :: "int list => (int list) list" where
"risers (Nil2) = Nil2"
| "risers (Cons2 y (Nil2)) = Cons2 (Cons2 y (Nil2)) (Nil2)"
| "risers (Cons2 y (Cons2 y2 xs)) =
     (if y <= y2 then
        case risers (Cons2 y2 xs) of
          | Nil2 => risers (Cons2 y2 xs)
          | Cons2 ys yss => Cons2 (Cons2 y ys) yss
        end
        else
        Cons2 (Cons2 y (Nil2)) (risers (Cons2 y2 xs)))"

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

fun mergingbu2 :: "(int list) list => int list" where
"mergingbu2 (Nil2) = Nil2"
| "mergingbu2 (Cons2 xs (Nil2)) = xs"
| "mergingbu2 (Cons2 xs (Cons2 z x2)) =
     mergingbu2 (pairwise (Cons2 xs (Cons2 z x2)))"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun msortbu2 :: "int list => int list" where
"msortbu2 x =
   dot
     (% (y :: (int list) list) => mergingbu2 y)
     (% (z :: int list) => risers z) x"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

(*hipster risers
          lmerge
          pairwise
          mergingbu2
          dot
          msortbu2
          and2
          ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (msortbu2 x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
