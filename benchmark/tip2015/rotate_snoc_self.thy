theory rotate_snoc_self
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun snoc :: "'a => 'a list => 'a list" where
  "snoc x (nil) = cons x (nil)"
  | "snoc x (cons z ys) = cons z (snoc x ys)"
  fun rotate :: "Nat => 'a list => 'a list" where
  "rotate (Z) y = y"
  | "rotate (S z) (nil) = nil"
  | "rotate (S z) (cons x2 x3) = rotate z (snoc x2 x3)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (n :: Nat) (xs :: 'a list) .
       (rotate n (append xs xs)) = (append (rotate n xs) (rotate n xs))"
    oops
end
