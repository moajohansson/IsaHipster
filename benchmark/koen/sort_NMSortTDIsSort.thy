theory sort_NMSortTDIsSort
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (Nil2) y = y"
  | "lmerge (Cons2 z x2) (Nil2) = Cons2 z x2"
  | "lmerge (Cons2 z x2) (Cons2 x3 x4) =
       (if z <= x3 then Cons2 z (lmerge x2 (Cons2 x3 x4)) else
          Cons2 x3 (lmerge (Cons2 z x2) x4))"
  fun length :: "'t list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (Nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (Cons2 z xs) else Cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = Nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S n)) = S (half n)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun nmsorttd :: "int list => int list" where
  "nmsorttd (Nil2) = Nil2"
  | "nmsorttd (Cons2 y (Nil2)) = Cons2 y (Nil2)"
  | "nmsorttd (Cons2 y (Cons2 x2 x3)) =
       lmerge
         (nmsorttd
            (take
               (half (length (Cons2 y (Cons2 x2 x3)))) (Cons2 y (Cons2 x2 x3))))
         (nmsorttd
            (drop
               (half (length (Cons2 y (Cons2 x2 x3)))) (Cons2 y (Cons2 x2 x3))))"
  hipster take lmerge length insert2 isort half drop nmsorttd
  theorem x0 :
    "!! (x :: int list) . (nmsorttd x) = (isort x)"
    oops
end
