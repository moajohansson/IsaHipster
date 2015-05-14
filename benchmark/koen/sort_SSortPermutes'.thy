theory sort_SSortPermutes'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  fun ssortminimum :: "int => int list => int" where
  "ssortminimum x (nil) = x"
  | "ssortminimum x (cons z ys) =
       (if z <= x then ssortminimum z ys else ssortminimum x ys)"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (nil) = True"
  | "null (cons y z) = False"
  fun elem :: "int => int list => bool" where
  "elem x (nil) = False"
  | "elem x (cons z ys) = or2 (x = z) (elem x ys)"
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
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (nil) y = null y"
  | "isPermutation (cons z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  theorem x0 :
    "!! (x :: int list) . isPermutation (ssort x) x"
    oops
end
