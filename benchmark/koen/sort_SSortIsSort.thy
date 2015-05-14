theory sort_SSortIsSort
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun ssortminimum :: "int => int list => int" where
  "ssortminimum x (nil) = x"
  | "ssortminimum x (cons z ys) =
       (if z <= x then ssortminimum z ys else ssortminimum x ys)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (nil) = cons x (nil)"
  | "insert2 x (cons z xs) =
       (if x <= z then cons x (cons z xs) else cons z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (nil) = nil"
  | "isort (cons y xs) = insert2 y (isort xs)"
  fun delete :: "int => int list => int list" where
  "delete x (nil) = nil"
  | "delete x (cons z ys) =
       (if x = z then ys else cons z (delete x ys))"
  fun ssort :: "int list => int list" where
  "ssort (nil) = nil"
  | "ssort (cons y ys) =
       cons
         (ssortminimum y ys)
         (ssort (delete (ssortminimum y ys) (cons y ys)))"
  theorem x0 :
    "!! (x :: int list) . (ssort x) = (isort x)"
    oops
end
