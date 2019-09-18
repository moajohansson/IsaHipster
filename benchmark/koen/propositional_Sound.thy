theory propositional_Sound
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype ('a, 'b) Pair2 = Pair "'a" "'b"

datatype Form =  "Form" "Form" | Not "Form" | Var "int"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun or3 :: "bool list => bool" where
"or3 (Nil2) = False"
| "or3 (Cons2 y xs) = or2 y (or3 xs)"

fun models3 :: "int => ((int, bool) Pair2) list => bool list" where
"models3 x (Nil2) = Nil2"
| "models3 x (Cons2 (Pair y2 True) x2) = models3 x x2"
| "models3 x (Cons2 (Pair y2 False) x2) =
     Cons2 (x = y2) (models3 x x2)"

fun fst :: "('a, 'b) Pair2 => 'a" where
"fst (Pair y z) = y"

fun filter :: "('t => bool) => 't list => 't list" where
"filter p (Nil2) = Nil2"
| "filter p (Cons2 y z) =
     (if p y then Cons2 y (filter p z) else filter p z)"

fun dot :: "('b => 'c) => ('a => 'b) => 'a => 'c" where
"dot x y z = x (y z)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun and2 :: "bool => bool => bool" where
"and2 True y = y"
| "and2 False y = False"

fun all :: "('t => bool) => 't list => bool" where
"all x (Nil2) = True"
| "all x (Cons2 z xs) = and2 (x z) (all x xs)"

fun 3 :: "int => ((int, bool) Pair2) list => bool list" where
"3 x (Nil2) = Nil2"
| "3 x (Cons2 (Pair y2 True) x2) = Cons2 (x = y2) (3 x x2)"
| "3 x (Cons2 (Pair y2 False) x2) = 3 x x2"

function models :: "Form => ((int, bool) Pair2) list =>
                  (((int, bool) Pair2) list) list"
         and
           models2 :: "Form => (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list"
         and
           models4 :: "Form => (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list" where
"models ( p q) y = models2 q (models p y)"
| "models (Not ( p2 q2)) y =
     append (models (Not p2) y) (models ( p2 (Not q2)) y)"
| "models (Not (Not p3)) y = models p3 y"
| "models (Not (Var x2)) y =
     (if ~ (or3 (3 x2 y)) then
        Cons2
          (Cons2
             (Pair x2 False)
             (filter
                (% (x3 :: (int, bool) Pair2) =>
                   dot
                     (% (x4 :: int) => x2 ~= x4) (% (x5 :: (int, bool) Pair2) => fst x5)
                     x3)
                y))
          (Nil2)
        else
        Nil2)"
| "models (Var x6) y =
     (if ~ (or3 (models3 x6 y)) then
        Cons2
          (Cons2
             (Pair x6 True)
             (filter
                (% (x7 :: (int, bool) Pair2) =>
                   dot
                     (% (x8 :: int) => x6 ~= x8) (% (x9 :: (int, bool) Pair2) => fst x9)
                     x7)
                y))
          (Nil2)
        else
        Nil2)"
| "models2 q (Nil2) = Nil2"
| "models2 q (Cons2 y z) = models4 q z (models q y)"
| "models4 q x (Nil2) = models2 q x"
| "models4 q x (Cons2 z x2) = Cons2 z (models4 q x x2)"
by pat_completeness auto

fun 2 :: "((int, bool) Pair2) list => Form => bool" where
"2 x ( p q) = and2 (2 x p) (2 x q)"
| "2 x (Not p2) = ~ (2 x p2)"
| "2 x (Var z) = or3 (3 z x)"

(*hipster or2
          or3
          models3
          fst
          filter
          dot
          append
          and2
          all
          3
          models
          models2
          models4
          2 *)

theorem x0 :
  "!! (p :: Form) .
     all (% (x :: ((int, bool) Pair2) list) => 2 x p) (models p (Nil2))"
  by (tactic \<open>Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1\<close>)

end
