theory prop_36
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun takeWhile :: "('a => bool) => 'a list => 'a list" where
  "takeWhile x (nil) = nil"
  | "takeWhile x (cons z xs) =
       (if x z then cons z (takeWhile x xs) else nil)"
  theorem x0 :
    "!! (xs :: 'a list) . (takeWhile (% (x :: 'a) => True) xs) = xs"
    oops
end
