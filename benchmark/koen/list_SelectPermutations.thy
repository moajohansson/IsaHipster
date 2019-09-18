theory list_SelectPermutations
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

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

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun isPermutation :: "int list => int list => bool" where
"isPermutation (Nil2) y = null y"
| "isPermutation (Cons2 z xs) y =
     and2 (elem z y) (isPermutation xs (delete z y))"

fun all :: "('t => bool) => 't list => bool" where
"all x (Nil2) = True"
| "all x (Cons2 z xs) = and2 (x z) (all x xs)"

(*hipster select2
          select
          propSelectPermutations
          or2
          null
          elem
          delete
          and2
          isPermutation
          all *)

theorem x0 :
  "!! (xs :: int list) .
     all
       (% (x :: int list) => isPermutation x xs)
       (propSelectPermutations (select xs))"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
