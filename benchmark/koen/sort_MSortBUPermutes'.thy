theory sort_MSortBUPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
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
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu :: "int list => int list" where
  "msortbu x =
     dot
       (% (y :: (int list) list) => mergingbu y)
       (% (z :: int list) => map2 (% (x2 :: int) => cons x2 (nil)) z) x"
  fun delete :: "int => int list => int list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if x = z then ys else cons z (delete x ys))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  theorem x0 :
    "!! (x :: int list) . isPermutation (msortbu x) x"
    oops
end
