theory list_SelectPermutations2
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

datatype Nat = Z | S "Nat"

fun select2 :: "'a => (('a, ('a list)) Pair2) list =>
                (('a, ('a list)) Pair2) list" where
"select2 x (Nil2) = Nil2"
| "select2 x (Cons2 (Pair y2 ys) x2) =
     Cons2 (Pair y2 (Cons2 x ys)) (select2 x x2)"

fun select :: "'a list => (('a, ('a list)) Pair2) list" where
"select (Nil2) = Nil2"
| "select (Cons2 y xs) = Cons2 (Pair y xs) (select2 y (select xs))"

fun propSelectPermutations :: "((int, (int list)) Pair2) list =>
                               (int list) list" where
"propSelectPermutations (Nil2) = Nil2"
| "propSelectPermutations (Cons2 (Pair y2 ys) z) =
     Cons2 (Cons2 y2 ys) (propSelectPermutations z)"

fun eq :: "Nat => Nat => bool" where
"eq (Z) (Z) = True"
| "eq (Z) (S z) = False"
| "eq (S x2) (Z) = False"
| "eq (S x2) (S y2) = eq x2 y2"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun count :: "int => int list => Nat" where
"count x (Nil2) = Z"
| "count x (Cons2 z xs) =
     (if x = z then S (count x xs) else count x xs)"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun all :: "('t => bool) => 't list => bool" where
"all x (Nil2) = True"
| "all x (Cons2 z xs) = and2 (x z) (all x xs)"

(*hipster select2
          select
          propSelectPermutations
          eq
          dot
          count
          and2
          all *)

theorem x0 :
  "!! (xs :: int list) (z :: int) .
     all
       (% (x :: int list) =>
          dot
            (% (y :: Nat) => eq (count z xs) y)
            (% (x2 :: int list) => count z x2) x)
       (propSelectPermutations (select xs))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
