theory prop_10
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (nil) = nil"
  | "rev (cons y xs) = append (rev xs) (cons y (nil))"
  theorem x0 :
    "!! (x :: 'a list) . (rev (rev x)) = x"
    oops
end
