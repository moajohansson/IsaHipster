theory prop_35
imports Main
imports "../../IsaHipster"
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun dropWhile :: "('a => bool) => 'a list => 'a list" where
  "dropWhile x (nil) = nil"
  | "dropWhile x (cons z xs) =
       (if x z then dropWhile x xs else cons z xs)"
  hipster dropWhile
  theorem x0 :
    "!! (xs :: 'a list) . (dropWhile (% (x :: 'a) => False) xs) = xs"
    oops
end
