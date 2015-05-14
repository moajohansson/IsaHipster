theory rotate_structural_mod
imports Main
begin
  datatype Nat = S "Nat" | Z
  datatype 'a List2 = Cons2 "'a" "'a List2" | Nil2
  fun take :: "Nat => 'a List2 => 'a List2" where
  "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  | "take (S z) (Nil2) = Nil2"
  | "take (Z) y = Nil2"
  fun minus :: "Nat => Nat => Nat" where
  "minus (S z) (S x2) = minus z x2"
  | "minus (S z) (Z) = S z"
  | "minus (Z) y = Z"
  fun mod2 :: "Nat => Nat => Nat => Nat" where
  "mod2 (S n) (S k) (S x2) = mod2 n k (S x2)"
  | "mod2 (S n) (Z) (S x2) = mod2 n x2 (S x2)"
  | "mod2 (Z) (S m) (S x2) = minus (S x2) (S m)"
  | "mod2 (Z) (Z) (S x2) = Z"
  | "mod2 x y (Z) = Z"
  fun mod3 :: "Nat => Nat => Nat" where
  "mod3 x y = mod2 x Z y"
  fun length :: "'a List2 => Nat" where
  "length (Cons2 y xs) = S (length xs)"
  | "length (Nil2) = Z"
  fun drop :: "Nat => 'a List2 => 'a List2" where
  "drop (S z) (Cons2 x2 x3) = drop z x3"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (Z) y = y"
  fun append :: "'a List2 => 'a List2 => 'a List2" where
  "append (Cons2 z xs) y = Cons2 z (append xs y)"
  | "append (Nil2) y = y"
  fun rotate :: "Nat => 'a List2 => 'a List2" where
  "rotate (S z) (Cons2 x2 x3) =
     rotate z (append x3 (Cons2 x2 (Nil2)))"
  | "rotate (S z) (Nil2) = Nil2"
  | "rotate (Z) y = y"
  theorem x0 :
    "!! (n :: Nat) (xs :: 'a List2) .
       (rotate n xs) =
         (append
            (drop (mod3 n (length xs)) xs) (take (mod3 n (length xs)) xs))"
    oops
end
