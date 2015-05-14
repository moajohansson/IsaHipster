theory list_SelectPermutations'
imports Main
begin
  datatype 'a list = nil | cons "'a" "'a list"
  datatype ('a, 'b) Pair2 = Pair "'a" "'b"
  datatype Nat = Z | S "Nat"
  fun select2 :: "'a => (('a, ('a list)) Pair2) list =>
                  (('a, ('a list)) Pair2) list" where
  "select2 x (nil) = nil"
  | "select2 x (cons (Pair y2 ys) x2) =
       cons (Pair y2 (cons x ys)) (select2 x x2)"
  fun select :: "'a list => (('a, ('a list)) Pair2) list" where
  "select (nil) = nil"
  | "select (cons y xs) = cons (Pair y xs) (select2 y (select xs))"
  fun propSelectPermutations :: "((int, (int list)) Pair2) list =>
                                 (int list) list" where
  "propSelectPermutations (nil) = nil"
  | "propSelectPermutations (cons (Pair y2 ys) z) =
       cons (cons y2 ys) (propSelectPermutations z)"
  fun eq :: "Nat => Nat => bool" where
  "eq (Z) (Z) = True"
  | "eq (Z) (S z) = False"
  | "eq (S x2) (Z) = False"
  | "eq (S x2) (S y2) = eq x2 y2"
  fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
  "dot x y z = x (y z)"
  fun count :: "int => int list => Nat" where
  "count x (nil) = Z"
  | "count x (cons z xs) =
       (if x = z then S (count x xs) else count x xs)"
  fun and2 :: "bool => bool => bool" where
  "and2 True y = y"
  | "and2 False y = False"
  fun all :: "('t => bool) => 't list => bool" where
  "all x (nil) = True"
  | "all x (cons z xs) = and2 (x z) (all x xs)"
  theorem x0 :
    "!! (xs :: int list) (z :: int) .
       all
         (% (x :: int list) =>
            dot
              (% (y :: Nat) => eq (count z xs) y)
              (% (x2 :: int list) => count z x2) x)
         (propSelectPermutations (select xs))"
    oops
end
