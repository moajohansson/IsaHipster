theory prop_47
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  fun insert2 :: "Nat => Nat list => Nat list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if le x z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun unequal :: "Nat => Nat => bool" where
  "unequal x y = ~ (equal2 x y)"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  hipster le insert2 equal2 unequal elem
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) (z :: Nat list) .
       (unequal x y) ==> ((elem x (insert2 y z)) = (elem x z))"
    oops
end
