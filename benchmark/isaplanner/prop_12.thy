theory prop_12
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun map2 :: "('a => 'b) => 'a list => 'b list" where
  "map2 x (Nil2) = Nil2"
  | "map2 x (Cons2 z xs) = Cons2 (x z) (map2 x xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster map2 drop *)
  theorem x0 :
    "!! (n :: Nat) (f :: ('a1 => 'a)) (xs :: 'a1 list) .
       (drop n (map2 f xs)) = (map2 f (drop n xs))"
    by (hipster_induct_schemes)
end
