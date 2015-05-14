theory sort_NMSortTDIsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  fun lmerge :: "int list => int list => int list" where
  "lmerge (nil) y = y"
  | "lmerge (cons z x2) (nil) = cons z x2"
  | "lmerge (cons z x2) (cons x3 x4) =
       (if z <= x3 then cons z (lmerge x2 (cons x3 x4)) else
          cons x3 (lmerge (cons z x2) x4))"
  fun length :: "'t list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S n)) = S (half n)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  fun nmsorttd :: "int list => int list" where
  "nmsorttd (nil) = nil"
  | "nmsorttd (cons y (nil)) = cons y (nil)"
  | "nmsorttd (cons y (cons x2 x3)) =
       lmerge
         (nmsorttd
            (take (half (length (cons y (cons x2 x3)))) (cons y (cons x2 x3))))
         (nmsorttd
            (drop
               (half (length (cons y (cons x2 x3)))) (cons y (cons x2 x3))))"
  theorem x0 :
    "!! (x :: int list) . (nmsorttd x) = (isort x)"
    oops
end
