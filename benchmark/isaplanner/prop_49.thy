theory prop_49
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (nil) = nil"
  | "butlast (cons y (nil)) = nil"
  | "butlast (cons y (cons x2 x3)) = cons y (butlast (cons x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun butlastConcat :: "'a list => 'a list => 'a list" where
  "butlastConcat x (nil) = butlast x"
  | "butlastConcat x (cons z x2) = append x (butlast (cons z x2))"
  hipster butlast append butlastConcat
  theorem x0 :
    "!! (xs :: 'a list) (ys :: 'a list) .
       (butlast (append xs ys)) = (butlastConcat xs ys)"
    oops
end
