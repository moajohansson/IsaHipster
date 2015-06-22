theory sort_BubSortPermutes'
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

fun elem :: "int => int list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"

fun delete :: "int => int list => int list" where
"delete x (Nil2) = Nil2"
| "delete x (Cons2 z ys) =
     (if x = z then ys else Cons2 z (delete x ys))"

fun bubble :: "int list => (bool, (int list)) Pair2" where
"bubble (Nil2) = Pair False (Nil2)"
| "bubble (Cons2 y (Nil2)) = Pair False (Cons2 y (Nil2))"
| "bubble (Cons2 y (Cons2 y2 xs)) =
     (if y <= y2 then
        case bubble (Cons2 y2 xs) of
          | Pair b6 ys5 =>
              (if y <= y2 then
                 (if y <= y2 then
                    case bubble (Cons2 y2 xs) of
                      | Pair b10 ys9 => Pair (or2 (~ (y <= y2)) b6) (Cons2 y ys9)
                    end
                    else
                    case bubble (Cons2 y xs) of
                      | Pair b9 ys8 => Pair (or2 (~ (y <= y2)) b6) (Cons2 y ys8)
                    end)
                 else
                 (if y <= y2 then
                    case bubble (Cons2 y2 xs) of
                      | Pair b8 ys7 => Pair (or2 (~ (y <= y2)) b6) (Cons2 y2 ys7)
                    end
                    else
                    case bubble (Cons2 y xs) of
                      | Pair b7 ys6 => Pair (or2 (~ (y <= y2)) b6) (Cons2 y2 ys6)
                    end))
        end
        else
        case bubble (Cons2 y xs) of
          | Pair c2 ys =>
              (if y <= y2 then
                 (if y <= y2 then
                    case bubble (Cons2 y2 xs) of
                      | Pair b5 ys4 => Pair (or2 (~ (y <= y2)) c2) (Cons2 y ys4)
                    end
                    else
                    case bubble (Cons2 y xs) of
                      | Pair b4 ys3 => Pair (or2 (~ (y <= y2)) c2) (Cons2 y ys3)
                    end)
                 else
                 (if y <= y2 then
                    case bubble (Cons2 y2 xs) of
                      | Pair b3 ys2 => Pair (or2 (~ (y <= y2)) c2) (Cons2 y2 ys2)
                    end
                    else
                    case bubble (Cons2 y xs) of
                      | Pair b2 zs => Pair (or2 (~ (y <= y2)) c2) (Cons2 y2 zs)
                    end))
        end)"

fun bubsort :: "int list => int list" where
"bubsort x =
   case bubble x of
     | Pair c ys =>
         (if c then
            case bubble x of | Pair b2 xs => bubsort xs
            end
            else
            x)
   end"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "int list => int list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

(*hipster or2 null elem delete bubble bubsort and2 isPermutation *)

theorem x0 :
  "!! (x :: int list) . isPermutation (bubsort x) x"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
