theory sort_MSortBU2IsSort
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun risers :: "int list => (int list) list" where
  "risers (Nil2) = Nil2"
  | "risers (Cons2 y (Nil2)) = Cons2 (Cons2 y (Nil2)) (Nil2)"
  | "risers (Cons2 y (Cons2 y2 xs)) =
       (if y <= y2 then
          case risers (Cons2 y2 xs) of
            | Nil2 => risers (Cons2 y2 xs)
            | Cons2 ys yss => Cons2 (Cons2 y ys) yss
          end
          else
          Cons2 (Cons2 y (Nil2)) (risers (Cons2 y2 xs)))"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (Nil2) y = y"
  | "lmerge (Cons2 z x2) (Nil2) = Cons2 z x2"
  | "lmerge (Cons2 z x2) (Cons2 x3 x4) =
       (if z <= x3 then Cons2 z (lmerge x2 (Cons2 x3 x4)) else
          Cons2 x3 (lmerge (Cons2 z x2) x4))"
  fun pairwise :: "(int list) list => (int list) list" where
  "pairwise (Nil2) = Nil2"
  | "pairwise (Cons2 xs (Nil2)) = Cons2 xs (Nil2)"
  | "pairwise (Cons2 xs (Cons2 ys xss)) =
       Cons2 (lmerge xs ys) (pairwise xss)"
  fun mergingbu2 :: "(int list) list => int list" where
  "mergingbu2 (Nil2) = Nil2"
  | "mergingbu2 (Cons2 xs (Nil2)) = xs"
  | "mergingbu2 (Cons2 xs (Cons2 z x2)) =
       mergingbu2 (pairwise (Cons2 xs (Cons2 z x2)))"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun msortbu2 :: "int list => int list" where
  "msortbu2 x =
     dot
       (% (y :: (int list) list) => mergingbu2 y)
       (% (z :: int list) => risers z) x"
  hipster risers
          lmerge
          pairwise
          mergingbu2
          insert2
          isort
          dot
          msortbu2
  theorem x0 :
    "!! (x :: int list) . (msortbu2 x) = (isort x)"
    oops
end
