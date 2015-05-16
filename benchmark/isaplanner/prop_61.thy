theory prop_61
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun last :: "Nat list => Nat" where
  "last (Nil2) = Z"
  | "last (Cons2 y (Nil2)) = y"
  | "last (Cons2 y (cons2 x2 x3)) = last (cons2 x2 x3)"
  fun lastOfTwo :: "Nat list => Nat list => Nat" where
  "lastOfTwo x (Nil2) = last x"
  | "lastOfTwo x (Cons2 z x2) = last (cons2 z x2)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  hipster last lastOfTwo append
  theorem x0 :
    "!! (xs :: Nat list) (ys :: Nat list) .
       (last (append xs ys)) = (lastOfTwo xs ys)"
    oops
end
