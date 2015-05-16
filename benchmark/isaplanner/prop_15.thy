theory prop_15
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
  | "lt (Z) (S z) = True"
  | "lt (S x2) (S z) = lt x2 z"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun ins :: "Nat => Nat list => Nat list" where
  "ins x (Nil2) = Cons2 x (nil2)"
  | "ins x (Cons2 z xs) =
       (if lt x z then Cons2 x (cons2 z xs) else cons2 z (ins x xs))"
  hipster lt len ins
  theorem x0 :
    "!! (x :: Nat) (xs :: Nat list) . (len (ins x xs)) = (S (len xs))"
    oops
end
