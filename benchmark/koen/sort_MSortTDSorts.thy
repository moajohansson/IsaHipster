theory sort_MSortTDSorts
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

fun ztake :: "int => 'a list => 'a list" where
"ztake x y =
   (if x = 0 then Nil2 else
      case y of
        | Nil2 => y
        | Cons2 z xs => Cons2 z (ztake (x - 1) xs)
      end)"

fun zlength :: "'a list => int" where
"zlength (Nil2) = 0"
| "zlength (Cons2 y xs) = 1 + (zlength xs)"

fun zdrop :: "int => 'a list => 'a list" where
"zdrop x y =
   (if x = 0 then y else
      case y of
        | Nil2 => y
        | Cons2 z xs => zdrop (x - 1) xs
      end)"

fun lmerge :: "int list => int list => int list" where
"lmerge (Nil2) y = y"
| "lmerge (Cons2 z x2) (Nil2) = Cons2 z x2"
| "lmerge (Cons2 z x2) (Cons2 x3 x4) =
     (if z <= x3 then Cons2 z (lmerge x2 (Cons2 x3 x4)) else
        Cons2 x3 (lmerge (Cons2 z x2) x4))"

fun msorttd :: "int list => int list" where
"msorttd (Nil2) = Nil2"
| "msorttd (Cons2 y (Nil2)) = Cons2 y (Nil2)"
| "msorttd (Cons2 y (Cons2 x2 x3)) =
     lmerge
       (msorttd
          (ztake
             (div (zlength (Cons2 y (Cons2 x2 x3))) 2) (Cons2 y (Cons2 x2 x3))))
       (msorttd
          (zdrop
             (div (zlength (Cons2 y (Cons2 x2 x3))) 2)
             (Cons2 y (Cons2 x2 x3))))"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

(*hipster ztake zlength zdrop lmerge msorttd and2 ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (msorttd x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
