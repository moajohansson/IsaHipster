theory prop_37
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
  fun elem :: "Nat => Nat list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z xs) = (if equal2 x z then True else elem x xs)"
  fun delete :: "Nat => Nat list => Nat list" where
  "delete x (Nil2) = nil2"
  | "delete x (Cons2 z xs) =
       (if equal2 x z then delete x xs else Cons2 z (delete x xs))"
  hipster equal2 elem delete
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . ~ (elem x (delete x xs))"
    oops
end
