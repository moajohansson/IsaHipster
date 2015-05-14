theory prop_51
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun butlast :: "'a list => 'a list" where
  "butlast (nil) = nil"
  | "butlast (cons y (nil)) = nil"
  | "butlast (cons y (cons x2 x3)) = cons y (butlast (cons x2 x3))"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (xs :: 'a list) (x :: 'a) .
       (butlast (append xs (cons x (nil)))) = xs"
    oops
end
