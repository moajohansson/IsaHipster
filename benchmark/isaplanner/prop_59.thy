theory prop_59
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (nil) = Z"
  | "last (cons y (nil)) = y"
  | "last (cons y (cons x2 x3)) = last (cons x2 x3)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  hipster last append
  theorem x0 :
    "!! (xs :: Nat list) (ys :: Nat list) .
       (ys = (nil)) ==> ((last (append xs ys)) = (last xs))"
    oops
end
