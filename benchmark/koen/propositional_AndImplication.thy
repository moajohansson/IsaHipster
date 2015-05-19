theory propositional_AndImplication
imports Main
        "../../IsaHipster"
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

fun null :: "'t list => bool" where
"null (Nil2) = True"
| "null (Cons2 y z) = False"

fun models4 :: "int => ((int, bool) Pair2) list => bool list" where
"models4 x (Nil2) = Nil2"
| "models4 x (Cons2 (Pair y2 True) x2) = models4 x x2"
| "models4 x (Cons2 (Pair y2 False) x2) =
     Cons2 (x = y2) (models4 x x2)"

fun models3 :: "int => ((int, bool) Pair2) list => bool list" where
"models3 x (Nil2) = Nil2"
| "models3 x (Cons2 (Pair y2 True) x2) =
     Cons2 (x = y2) (models3 x x2)"
| "models3 x (Cons2 (Pair y2 False) x2) = models3 x x2"

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

function models :: "Form => ((int, bool) Pair2) list =>
                  (((int, bool) Pair2) list) list"
         and
           models2 :: "Form => (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list"
         and
           models5 :: "Form => (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list =>
                     (((int, bool) Pair2) list) list" where
"models ( p q) y = models2 q (models p y)"
| "models (Not ( p2 q2)) y =
     append (models (Not p2) y) (models ( p2 (Not q2)) y)"
| "models (Not (Not p3)) y = models p3 y"
| "models (Not (Var x2)) y =
     (if ~ (or3 (models3 x2 y)) then
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
     (if ~ (or3 (models4 x6 y)) then
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
| "models2 q (Cons2 y z) = models5 q z (models q y)"
| "models5 q x (Nil2) = models2 q x"
| "models5 q x (Cons2 z x2) = Cons2 z (models5 q x x2)"
by pat_completeness auto

fun valid :: "Form => bool" where
"valid x = null (models (Not x) (Nil2))"

(*hipster or2
          or3
          null
          models4
          models3
          fst
          filter
          dot
          append
          models
          models2
          models5
          valid *)

theorem x0 :
  "!! (p :: Form) (q :: Form) . (valid ( p q)) ==> (valid q)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
