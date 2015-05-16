theory sort_SSortIsSort
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  fun ssortminimum :: "int => int list => int" where
  "ssortminimum x (Nil2) = x"
  | "ssortminimum x (Cons2 z ys) =
       (if z <= x then ssortminimum z ys else ssortminimum x ys)"
  fun insert2 :: "int => int list => int list" where
  "insert2 x (Nil2) = Cons2 x (nil2)"
  | "insert2 x (Cons2 z xs) =
       (if x <= z then Cons2 x (cons2 z xs) else cons2 z (insert2 x xs))"
  fun isort :: "int list => int list" where
  "isort (Nil2) = nil2"
  | "isort (Cons2 y xs) = insert2 y (isort xs)"
  fun delete :: "int => int list => int list" where
  "delete x (Nil2) = nil2"
  | "delete x (Cons2 z ys) =
       (if x = z then ys else Cons2 z (delete x ys))"
  fun ssort :: "int list => int list" where
  "ssort (Nil2) = nil2"
  | "ssort (Cons2 y ys) =
       Cons2
         (ssortminimum y ys)
         (ssort (delete (ssortminimum y ys) (Cons2 y ys)))"
  hipster ssortminimum insert2 isort delete ssort
  theorem x0 :
    "!! (x :: int list) . (ssort x) = (isort x)"
    oops
end
