theory prop_67
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = Nil2"
  | "butlast (Cons2 y (Nil2)) = Nil2"
  | "butlast (Cons2 y (Cons2 x2 x3)) =
       Cons2 y (butlast (Cons2 x2 x3))"
  (*hipster minus len butlast *)
  theorem x0 :
    "!! (xs :: 'a list) . (len (butlast xs)) = (minus (len xs) (S Z))"
    by (hipster_induct_schemes)
end
