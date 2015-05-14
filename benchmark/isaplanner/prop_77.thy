theory prop_77
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun sorted :: "Nat list => bool" where
  "sorted (nil) = True"
  | "sorted (cons y (nil)) = True"
  | "sorted (cons y (cons y2 ys)) =
       (if le y y2 then sorted (cons y2 ys) else False)"
  fun insort :: "Nat => Nat list => Nat list" where
  "insort x (nil) = cons x (nil)"
  | "insort x (cons z xs) =
       (if le x z then cons x (cons z xs) else cons z (insort x xs))"
  hipster le sorted insort
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) .
       (sorted xs) ==> (sorted (insort x xs))"
    oops
end
