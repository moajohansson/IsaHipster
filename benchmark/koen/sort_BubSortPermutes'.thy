theory sort_BubSortPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
  fun delete :: "int => int list => int list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if x = z then ys else cons z (delete x ys))"
  fun bubble :: "int list => (bool, (int list)) Pair2" where
  "bubble (nil) = Pair False (nil)"
  | "bubble (cons y (nil)) = Pair False (cons y (nil))"
  | "bubble (cons y (cons y2 xs)) =
       (if y <= y2 then
          case bubble (cons y2 xs) of
            | Pair b6 ys5 =>
                (if y <= y2 then
                   (if y <= y2 then
                      case bubble (cons y2 xs) of
                        | Pair b10 ys9 => Pair (or2 (~ (y <= y2)) b6) (cons y ys9)
                      end
                      else
                      case bubble (cons y xs) of
                        | Pair b9 ys8 => Pair (or2 (~ (y <= y2)) b6) (cons y ys8)
                      end)
                   else
                   (if y <= y2 then
                      case bubble (cons y2 xs) of
                        | Pair b8 ys7 => Pair (or2 (~ (y <= y2)) b6) (cons y2 ys7)
                      end
                      else
                      case bubble (cons y xs) of
                        | Pair b7 ys6 => Pair (or2 (~ (y <= y2)) b6) (cons y2 ys6)
                      end))
          end
          else
          case bubble (cons y xs) of
            | Pair c2 ys =>
                (if y <= y2 then
                   (if y <= y2 then
                      case bubble (cons y2 xs) of
                        | Pair b5 ys4 => Pair (or2 (~ (y <= y2)) c2) (cons y ys4)
                      end
                      else
                      case bubble (cons y xs) of
                        | Pair b4 ys3 => Pair (or2 (~ (y <= y2)) c2) (cons y ys3)
                      end)
                   else
                   (if y <= y2 then
                      case bubble (cons y2 xs) of
                        | Pair b3 ys2 => Pair (or2 (~ (y <= y2)) c2) (cons y2 ys2)
                      end
                      else
                      case bubble (cons y xs) of
                        | Pair b2 zs => Pair (or2 (~ (y <= y2)) c2) (cons y2 zs)
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
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  theorem x0 :
    "!! (x :: int list) . isPermutation (bubsort x) x"
    oops
end
