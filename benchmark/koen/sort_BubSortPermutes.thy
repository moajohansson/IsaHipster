theory sort_BubSortPermutes
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

datatype Nat = Z | S "Nat"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun count :: "int => int list => Nat" where
"count x (Nil2) = Z"
| "count x (Cons2 z xs) =
     (if x = z then S (count x xs) else count x xs)"

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

(*hipster or2 count bubble bubsort *)

theorem x0 :
  "!! (x :: int) (y :: int list) .
     (count x (bubsort y)) = (count x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
