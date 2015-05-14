theory prop_43
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (nil) = nil"
  | "takeWhile x (cons z xs) =
       (if x z then cons z (takeWhile x xs) else nil)"
  fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (nil) = nil"
  | "dropWhile x (cons z xs) =
       (if x z then dropWhile x xs else cons z xs)"
  fun append :: "'a list => 'a list => 'a list" where
  "append (nil) y = y"
  | "append (cons z xs) y = cons z (append xs y)"
  theorem x0 :
    "!! (p :: ('a => bool)) (xs :: 'a list) .
       (append (takeWhile p xs) (dropWhile p xs)) = xs"
    oops
end
