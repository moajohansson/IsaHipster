theory sort_SSortSorts
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun ssortminimum :: "int => int list => int" where
  "ssortminimum x (nil) = x"
  | "ssortminimum x (cons z ys) =
       (if z <= x then ssortminimum z ys else ssortminimum x ys)"
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
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun ordered :: "int list => bool" where
  "ordered (nil) = True"
  | "ordered (cons y (nil)) = True"
  | "ordered (cons y (cons y2 xs)) =
       and2 (y <= y2) (ordered (cons y2 xs))"
  theorem x0 :
    "!! (x :: int list) . ordered (ssort x)"
    oops
end
