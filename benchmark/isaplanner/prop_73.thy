theory A
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun filter :: "'a => bool => 'a list => 'a list" where
  "filter x (nil) = nil"
  | "filter x (cons z xs) =
       (if x z then cons z (filter x xs) else filter x xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  fun rev :: "'a list => 'a list" where
  "rev (nil) = nil"
  | "rev (cons y xs) = append (rev xs) (cons y (nil))"
  theorem x0 :
    "!! (p :: 'a => bool) (xs :: 'a list) .
       (rev (filter p xs)) = (filter p (rev xs))"
    oops
end
