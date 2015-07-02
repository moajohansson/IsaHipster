theory sort_NStoogeSortIsSort
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

datatype Nat = Z | S "Nat"

fun third :: "Nat => Nat" where
"third (Z) = Z"
| "third (S (Z)) = Z"
| "third (S (S (Z))) = Z"
| "third (S (S (S n))) = S (third n)"

fun take :: "Nat => 'a list => 'a list" where
"take (Z) y = Nil2"
| "take (S z) (Nil2) = Nil2"
| "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"

fun sort2 :: "int => int => int list" where
"sort2 x y =
   (if x <= y then Cons2 x (Cons2 y (Nil2)) else
      Cons2 y (Cons2 x (Nil2)))"

fun length :: "'t list => Nat" where
"length (Nil2) = Z"
| "length (Cons2 y xs) = S (length xs)"

fun insert2 :: "int => int list => int list" where
"insert2 x (Nil2) = Cons2 x (Nil2)"
| "insert2 x (Cons2 z xs) =
     (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"

fun isort :: "int list => int list" where
"isort (Nil2) = Nil2"
| "isort (Cons2 y xs) = insert2 y (isort xs)"

fun drop :: "Nat => 'a list => 'a list" where
"drop (Z) y = y"
| "drop (S z) (Nil2) = Nil2"
| "drop (S z) (Cons2 x2 x3) = drop z x3"

fun splitAt :: "Nat => 'a list =>
              (('a list), ('a list)) Pair2" where
"splitAt x y = Pair (take x y) (drop x y)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun reverse :: "'t list => 't list" where
"reverse (Nil2) = Nil2"
| "reverse (Cons2 y xs) = append (reverse xs) (Cons2 y (Nil2))"

function nstooge1sort2 :: "int list => int list"
         and nstoogesort :: "int list => int list"
         and nstooge1sort1 :: "int list => int list" where
"nstooge1sort2 x =
   case splitAt (third (length x)) (reverse x) of
     | Pair ys zs =>
         case splitAt (third (length x)) (reverse x) of
           | Pair xs zs2 => append (nstoogesort zs) (reverse xs)
         end
   end"
| "nstoogesort (Nil2) = Nil2"
| "nstoogesort (Cons2 y (Nil2)) = Cons2 y (Nil2)"
| "nstoogesort (Cons2 y (Cons2 y2 (Nil2))) = sort2 y y2"
| "nstoogesort (Cons2 y (Cons2 y2 (Cons2 x3 x4))) =
     nstooge1sort2
       (nstooge1sort1 (nstooge1sort2 (Cons2 y (Cons2 y2 (Cons2 x3 x4)))))"
| "nstooge1sort1 x =
     case splitAt (third (length x)) x of
       | Pair ys zs =>
           case splitAt (third (length x)) x of
             | Pair xs zs2 => append ys (nstoogesort zs2)
           end
     end"
by pat_completeness auto

(*hipster third
          take
          sort2
          length
          insert2
          isort
          drop
          splitAt
          append
          reverse
          nstooge1sort2
          nstoogesort
          nstooge1sort1 *)

theorem x0 :
  "!! (x :: int list) . (nstoogesort x) = (isort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
