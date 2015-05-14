theory sort_MSortBU2Sorts
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
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu2 :: "int list => int list" where
  "msortbu2 x =
     dot
       (% (y :: (int list) list) => mergingbu2 y)
       (% (z :: int list) => risers z) x"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (y <= y2) (ordered (cons y2 xs))"
  theorem x0 :
    "!! (x :: int list) . ordered (msortbu2 x)"
    oops
end
