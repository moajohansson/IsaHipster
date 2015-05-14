theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype 'a 'b Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun zip :: "'a list => 'b list => ('a 'b Pair2) list" where
  "zip (nil) y = nil"
  | "zip (cons z x2) (nil) = nil"
  | "zip (cons z x2) (cons x3 x4) = cons (Pair z x3) (zip x2 x4)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (nil) = nil"
  | "drop (S z) (cons x2 x3) = drop z x3"
  theorem x0 :
    "!! (n :: Nat) (xs :: 'a list) (ys :: 'b list) .
       (drop n (zip xs ys)) = (zip (drop n xs) (drop n ys))"
    oops
end
