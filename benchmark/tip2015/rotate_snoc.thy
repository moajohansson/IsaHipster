theory rotate_snoc
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
  fun length :: "'a list => Nat" where
  "length (nil) = Z"
  | "length (cons y xs) = S (length xs)"
  theorem x0 :
    "!! (xs :: 'a list) . (rotate (length xs) xs) = xs"
    oops
end
