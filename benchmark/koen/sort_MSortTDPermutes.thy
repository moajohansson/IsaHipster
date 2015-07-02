theory sort_MSortTDPermutes
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

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

fun count :: "int => int list => Nat" where
"count x (Nil2) = Z"
| "count x (Cons2 z xs) =
     (if x = z then S (count x xs) else count x xs)"

(*hipster ztake zlength zdrop lmerge msorttd count *)

theorem x0 :
  "!! (x :: int) (y :: int list) .
     (count x (msorttd y)) = (count x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
