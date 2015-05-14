theory prop_39
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun count :: "Nat => Nat list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z ys) =
       (if equal2 x z then S (count x ys) else count x ys)"
  hipster plus equal2 count
  theorem x0 :
    "!! (n :: Nat) (x :: Nat) (xs :: Nat list) .
       (plus (count n (cons x (nil))) (count n xs)) =
         (count n (cons x xs))"
    oops
end
