theory sort_MSortBU2IsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun risers :: "int list => (int list) list" where
  "risers (nil) = nil"
  | "risers (cons y (nil)) = cons (cons y (nil)) (nil)"
  | "risers (cons y (cons y2 xs)) =
       (if y <= y2 then
          case risers (cons y2 xs) of
            | nil => risers (cons y2 xs)
            | cons ys yss => cons (cons y ys) yss
          end
          else
          cons (cons y (nil)) (risers (cons y2 xs)))"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (nil) y = y"
  | "lmerge (cons z x2) (nil) = cons z x2"
  | "lmerge (cons z x2) (cons x3 x4) =
       (if z <= x3 then cons z (lmerge x2 (cons x3 x4)) else
          cons x3 (lmerge (cons z x2) x4))"
  fun pairwise :: "(int list) list => (int list) list" where
  "pairwise (nil) = nil"
  | "pairwise (cons xs (nil)) = cons xs (nil)"
  | "pairwise (cons xs (cons ys xss)) =
       cons (lmerge xs ys) (pairwise xss)"
  fun mergingbu2 :: "(int list) list => int list" where
  "mergingbu2 (nil) = nil"
  | "mergingbu2 (cons xs (nil)) = xs"
  | "mergingbu2 (cons xs (cons z x2)) =
       mergingbu2 (pairwise (cons xs (cons z x2)))"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu2 :: "int list => int list" where
  "msortbu2 x =
     dot
       (% (y :: (int list) list) => mergingbu2 y)
       (% (z :: int list) => risers z) x"
  theorem x0 :
    "!! (x :: int list) . (msortbu2 x) = (isort x)"
    oops
end
