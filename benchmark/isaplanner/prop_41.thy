theory prop_41
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = nil2"
  | "take (S z) (Cons2 x2 x3) = cons2 x2 (take z x3)"
  fun map2 :: "('a => 'b) => 'a list => 'b list" where
  "map2 x (Nil2) = nil2"
  | "map2 x (Cons2 z xs) = cons2 (x z) (map2 x xs)"
  hipster take map2
  theorem x0 :
    "!! (n :: Nat) (f :: ('a1 => 'a)) (xs :: 'a1 list) .
       (take n (map2 f xs)) = (map2 f (take n xs))"
    oops
end
