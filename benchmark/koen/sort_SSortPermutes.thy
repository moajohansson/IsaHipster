theory sort_SSortPermutes
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype Nat = Z | S "Nat"
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
  fun count :: "int => int list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if x = z then S (count x xs) else count x xs)"
  theorem x0 :
    "!! (x :: int) (y :: int list) . (count x (ssort y)) = (count x y)"
    oops
end
