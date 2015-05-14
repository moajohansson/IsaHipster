theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil"
  | "take (S z) (nil) = nil"
  | "take (S z) (cons x2 x3) = cons x2 (take z x3)"
  fun map2 :: "'a => 'b => 'a list => 'b list" where
  "map2 x (nil) = nil"
  | "map2 x (cons z xs) = cons (x z) (map2 x xs)"
  theorem x0 :
    "!! (n :: Nat) (f :: 'a1 => 'a) (xs :: 'a1 list) .
       (take n (map2 f xs)) = (map2 f (take n xs))"
    oops
end
