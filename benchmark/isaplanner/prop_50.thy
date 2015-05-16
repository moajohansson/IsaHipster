theory prop_50
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = nil2"
  | "butlast (Cons2 y (Nil2)) = nil2"
  | "butlast (Cons2 y (cons2 x2 x3)) =
       Cons2 y (butlast (cons2 x2 x3))"
  hipster take minus len butlast
  theorem x0 :
    "!! (xs :: 'a list) .
       (butlast xs) = (take (minus (len xs) (S Z)) xs)"
    oops
end
