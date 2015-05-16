theory prop_49
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (Nil2) = nil2"
  | "butlast (Cons2 y (Nil2)) = nil2"
  | "butlast (Cons2 y (cons2 x2 x3)) =
       Cons2 y (butlast (cons2 x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (Nil2) y = y"
  | "append (Cons2 z xs) y = cons2 z (append xs y)"
  fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (Nil2) = butlast x"
  | "butlastConcat x (Cons2 z x2) = append x (butlast (cons2 z x2))"
  hipster butlast append butlastConcat
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a list) .
       (butlast (append xs ys)) = (butlastConcat xs ys)"
    oops
end
