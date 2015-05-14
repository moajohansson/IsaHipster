theory sort_MSortBUIsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun map2 :: "('t2 => 't) => 't2 list => 't list" where
  "map2 f (nil) = nil"
  | "map2 f (cons y z) = cons (f y) (map2 f z)"
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
  fun mergingbu :: "(int list) list => int list" where
  "mergingbu (nil) = nil"
  | "mergingbu (cons xs (nil)) = xs"
  | "mergingbu (cons xs (cons z x2)) =
       mergingbu (pairwise (cons xs (cons z x2)))"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu :: "int list => int list" where
  "msortbu x =
     dot
       (% (y :: (int list) list) => mergingbu y)
       (% (z :: int list) => map2 (% (x2 :: int) => cons x2 (nil)) z) x"
  theorem x0 :
    "!! (x :: int list) . (msortbu x) = (isort x)"
    oops
end
