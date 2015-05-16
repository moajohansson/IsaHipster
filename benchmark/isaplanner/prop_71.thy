theory prop_71
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (nil2)"
  | "ins x (Cons2 z xs) =
       (if lt x z then Cons2 x (cons2 z xs) else cons2 z (ins x xs))"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  hipster lt ins equal2 elem
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) (xs :: Nat list) .
       (~ (equal2 x y)) ==> ((elem x (ins y xs)) = (elem x xs))"
    oops
end
