theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun map2 :: "'a => 'b => 'a list => 'b list" where
  "map2 x (nil) = nil"
  | "map2 x (cons z xs) = cons (x z) (map2 x xs)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  theorem x0 :
    "!! (n :: Nat) (f :: 'a1 => 'a) (xs :: 'a1 list) .
       (drop n (map2 f xs)) = (map2 f (drop n xs))"
    oops
end
