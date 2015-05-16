theory prop_28
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
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  (*hipster equal2 elem append *)
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) .
       elem x (append xs (Cons2 x (Nil2)))"
    by (hipster_induct_schemes)
end
