theory prop_72
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
  | "minus (S z) (Z) = S z"
  | "minus (S z) (S x2) = minus z x2"
  fun len :: "'a list => Nat" where
  "len (Nil2) = Z"
  | "len (Cons2 y xs) = S (len xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = Cons2 z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (Nil2) = Nil2"
  | "rev (Cons2 y xs) = append (rev xs) (Cons2 y (Nil2))"
  (*hipster take minus len drop append rev *)
  theorem x0 :
    "!! (i :: Nat) (xs :: 'a list) .
       (rev (drop i xs)) = (take (minus (len xs) i) (rev xs))"
    by (hipster_induct_schemes)
end
