theory prop_01
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  hipster take drop append
  theorem x0 :
    "!! (n :: Nat) (xs :: 'a list) .
       (append (take n xs) (drop n xs)) = xs"
    oops
end
