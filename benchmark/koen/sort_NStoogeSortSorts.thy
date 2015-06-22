theory sort_NStoogeSortSorts
imports Main
        "../../IsaHipster"
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

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun ordered :: "int list => bool" where
"ordered (Nil2) = True"
| "ordered (Cons2 y (Nil2)) = True"
| "ordered (Cons2 y (Cons2 y2 xs)) =
     and2 (y <= y2) (ordered (Cons2 y2 xs))"

(*hipster third
          take
          sort2
          length
          drop
          splitAt
          append
          reverse
          nstooge1sort2
          nstoogesort
          nstooge1sort1
          and2
          ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (nstoogesort x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
