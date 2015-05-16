theory sort_NMSortTDPermutes
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (Nil2) y = y"
  | "lmerge (Cons2 z x2) (Nil2) = cons2 z x2"
  | "lmerge (Cons2 z x2) (cons2 x3 x4) =
       (if z <= x3 then Cons2 z (lmerge x2 (cons2 x3 x4)) else
          Cons2 x3 (lmerge (cons2 z x2) x4))"
  fun length :: "'t list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S n)) = S (half n)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun nmsorttd :: "int list => int list" where
  "nmsorttd (Nil2) = nil2"
  | "nmsorttd (Cons2 y (Nil2)) = cons2 y (nil2)"
  | "nmsorttd (Cons2 y (cons2 x2 x3)) =
       lmerge
         (nmsorttd
            (take
               (half (length (Cons2 y (cons2 x2 x3)))) (cons2 y (cons2 x2 x3))))
         (nmsorttd
            (drop
               (half (length (Cons2 y (cons2 x2 x3)))) (cons2 y (cons2 x2 x3))))"
  fun count :: "int => int list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z xs) =
       (if x = z then S (count x xs) else count x xs)"
  hipster take lmerge length half drop nmsorttd count
  theorem x0 :
    "!! (x :: int) (y :: int list) .
       (count x (nmsorttd y)) = (count x y)"
    oops
end
