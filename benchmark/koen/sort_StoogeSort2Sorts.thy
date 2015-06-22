theory sort_StoogeSort2Sorts
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

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

fun zsplitAt :: "int => 'a list =>
                 (('a list), ('a list)) Pair2" where
"zsplitAt x y = Pair (ztake x y) (zdrop x y)"

fun sort2 :: "int => int => int list" where
"sort2 x y =
   (if x <= y then Cons2 x (Cons2 y (Nil2)) else
      Cons2 y (Cons2 x (Nil2)))"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

function stooge2sort2 :: "int list => int list"
         and stoogesort2 :: "int list => int list"
         and stooge2sort1 :: "int list => int list" where
"stooge2sort2 x =
   case zsplitAt (div ((2 * (zlength x)) + 1) 3) x of
     | Pair ys zs =>
         case zsplitAt (div ((2 * (zlength x)) + 1) 3) x of
           | Pair xs zs2 => append (stoogesort2 ys) zs2
         end
   end"
| "stoogesort2 (Nil2) = Nil2"
| "stoogesort2 (Cons2 y (Nil2)) = Cons2 y (Nil2)"
| "stoogesort2 (Cons2 y (Cons2 y2 (Nil2))) = sort2 y y2"
| "stoogesort2 (Cons2 y (Cons2 y2 (Cons2 x3 x4))) =
     stooge2sort2
       (stooge2sort1 (stooge2sort2 (Cons2 y (Cons2 y2 (Cons2 x3 x4)))))"
| "stooge2sort1 x =
     case zsplitAt (div (zlength x) 3) x of
       | Pair ys zs =>
           case zsplitAt (div (zlength x) 3) x of
             | Pair xs zs2 => append ys (stoogesort2 zs2)
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

(*hipster ztake
          zlength
          zdrop
          zsplitAt
          sort2
          append
          stooge2sort2
          stoogesort2
          stooge2sort1
          and2
          ordered *)

theorem x0 :
  "!! (x :: int list) . ordered (stoogesort2 x)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
