theory sort_NMSortTDPermutes'
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
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
  fun length :: "'t list => Nat" where
  "length (Nil2) = Z"
  | "length (Cons2 y xs) = S (length xs)"
  fun half :: "Nat => Nat" where
  "half (Z) = Z"
  | "half (S (Z)) = Z"
  | "half (S (S n)) = S (half n)"
  fun elem :: "int => int list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"
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
  hipster take
          or2
          null
          lmerge
          length
          half
          elem
          drop
          nmsorttd
          delete
          and2
          isPermutation
  theorem x0 :
    "!! (x :: int list) . isPermutation (nmsorttd x) x"
    oops
end
