theory prop_53
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (Nil2) = Cons2 x (Nil2)"
  | "insort x (Cons2 z xs) =
       (if le x z then Cons2 x (Cons2 z xs) else Cons2 z (insort x xs))"
  fun sort :: "Nat list => Nat list" where
  "sort (Nil2) = Nil2"
  | "sort (Cons2 y xs) = insort y (sort xs)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (Nil2) = Z"
  | "count x (Cons2 z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  (*hipster le insort sort equal2 count *)
  theorem x0 :
    "!! (n :: Nat) (xs :: Nat list) .
       (count n xs) = (count n (sort xs))"
    by (hipster_induct_schemes)
end
