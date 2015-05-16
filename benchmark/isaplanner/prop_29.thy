theory prop_29
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun equal2 :: "Nat => Nat => bool" where
  "equal2 (Z) (Z) = True"
  | "equal2 (Z) (S z) = False"
  | "equal2 (S x2) (Z) = False"
  | "equal2 (S x2) (S y2) = equal2 x2 y2"
  fun ins1 :: "Nat => Nat list => Nat list" where
  "ins1 x (Nil2) = Cons2 x (nil2)"
  | "ins1 x (Cons2 z xs) =
       (if equal2 x z then Cons2 z xs else cons2 z (ins1 x xs))"
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  hipster equal2 ins1 elem
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . elem x (ins1 x xs)"
    oops
end
