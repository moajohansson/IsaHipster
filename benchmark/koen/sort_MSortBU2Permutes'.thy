theory sort_MSortBU2Permutes'
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun risers :: "int list => (int list) list" where
  "risers (Nil2) = nil2"
  | "risers (Cons2 y (Nil2)) = cons2 (cons2 y (nil2)) (nil2)"
  | "risers (Cons2 y (cons2 y2 xs)) =
       (if y <= y2 then
          case risers (Cons2 y2 xs) of
            | Nil2 => risers (Cons2 y2 xs)
            | Cons2 ys yss => cons2 (cons2 y ys) yss
          end
          else
          Cons2 (cons2 y (Nil2)) (risers (cons2 y2 xs)))"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (Nil2) = True"
  | "null (Cons2 y z) = False"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (Nil2) y = y"
  | "lmerge (Cons2 z x2) (Nil2) = cons2 z x2"
  | "lmerge (Cons2 z x2) (cons2 x3 x4) =
       (if z <= x3 then Cons2 z (lmerge x2 (cons2 x3 x4)) else
          Cons2 x3 (lmerge (cons2 z x2) x4))"
  fun pairwise :: "(int list) list => (int list) list" where
  "pairwise (Nil2) = nil2"
  | "pairwise (Cons2 xs (Nil2)) = cons2 xs (nil2)"
  | "pairwise (Cons2 xs (cons2 ys xss)) =
       Cons2 (lmerge xs ys) (pairwise xss)"
  fun mergingbu2 :: "(int list) list => int list" where
  "mergingbu2 (Nil2) = nil2"
  | "mergingbu2 (Cons2 xs (Nil2)) = xs"
  | "mergingbu2 (Cons2 xs (cons2 z x2)) =
       mergingbu2 (pairwise (Cons2 xs (cons2 z x2)))"
  fun elem :: "int => int list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu2 :: "int list => int list" where
  "msortbu2 x =
     dot
       (% (y :: (int list) list) => mergingbu2 y)
       (% (z :: int list) => risers z) x"
  fun delete :: "int => int list => int list" where
  "delete x (Nil2) = nil2"
  | "delete x (Cons2 z ys) =
       (if x = z then ys else Cons2 z (delete x ys))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (Nil2) y = null y"
  | "isPermutation (Cons2 z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  hipster risers
          or2
          null
          lmerge
          pairwise
          mergingbu2
          elem
          dot
          msortbu2
          delete
          and2
          isPermutation
  theorem x0 :
    "!! (x :: int list) . isPermutation (msortbu2 x) x"
    oops
end
