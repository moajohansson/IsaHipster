theory prop_63
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
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (cons2 x2 x3)) = last (cons2 x2 x3)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  hipster lt len last drop
  theorem x0 :
    "!! (n :: Nat) (xs :: Nat list) .
       (lt n (len xs)) ==> ((last (drop n xs)) = (last xs))"
    oops
end
