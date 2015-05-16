theory sort_BubSortSorts
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun bubble :: "int list => (bool, (int list)) Pair2" where
  "bubble (Nil2) = Pair False (nil2)"
  | "bubble (Cons2 y (Nil2)) = Pair False (cons2 y (nil2))"
  | "bubble (Cons2 y (cons2 y2 xs)) =
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
  fun ordered :: "int list => bool" where
  "ordered (Nil2) = True"
  | "ordered (Cons2 y (Nil2)) = True"
  | "ordered (Cons2 y (cons2 y2 xs)) =
       and2 (y <= y2) (ordered (Cons2 y2 xs))"
  hipster or2 bubble bubsort and2 ordered
  theorem x0 :
    "!! (x :: int list) . ordered (bubsort x)"
    oops
end
