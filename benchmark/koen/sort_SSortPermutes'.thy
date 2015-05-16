theory sort_SSortPermutes'
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun ssortminimum :: "int => int list => int" where
  "ssortminimum x (Nil2) = x"
  | "ssortminimum x (Cons2 z ys) =
       (if z <= x then ssortminimum z ys else ssortminimum x ys)"
  fun or2 :: "bool => bool => bool" where
  "or2 True y = True"
  | "or2 False y = y"
  fun null :: "'t list => bool" where
  "null (Nil2) = True"
  | "null (Cons2 y z) = False"
  fun elem :: "int => int list => bool" where
  "elem x (Nil2) = False"
  | "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"
  fun delete :: "int => int list => int list" where
  "delete x (Nil2) = Nil2"
  | "delete x (Cons2 z ys) =
       (if x = z then ys else Cons2 z (delete x ys))"
  fun ssort :: "int list => int list" where
  "ssort (Nil2) = Nil2"
  | "ssort (Cons2 y ys) =
       Cons2
         (ssortminimum y ys)
         (ssort (delete (ssortminimum y ys) (Cons2 y ys)))"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun isPermutation :: "int list => int list => bool" where
  "isPermutation (Nil2) y = null y"
  | "isPermutation (Cons2 z xs) y =
       and2 (elem z y) (isPermutation xs (delete z y))"
  hipster ssortminimum or2 null elem delete ssort and2 isPermutation
  theorem x0 :
    "!! (x :: int list) . isPermutation (ssort x) x"
    oops
end
