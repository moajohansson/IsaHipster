theory subst_SubstFreeNo
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Expr = Var "int" | Lam "int" "Expr" | App "Expr" "Expr"

fun or2 :: "bool => bool => bool" where
"or2 True y = True"
| "or2 False y = y"

fun newmaximum :: "int => int list => int" where
"newmaximum x (Nil2) = x"
| "newmaximum x (Cons2 z ys) =
     (if x <= z then newmaximum z ys else newmaximum x ys)"

fun new :: "int list => int" where
"new x = (newmaximum 0 x) + 1"

fun filter :: "('t => bool) => 't list => 't list" where
"filter p (Nil2) = Nil2"
| "filter p (Cons2 y z) =
     (if p y then Cons2 y (filter p z) else filter p z)"

fun elem :: "int => int list => bool" where
"elem x (Nil2) = False"
| "elem x (Cons2 z ys) = or2 (x = z) (elem x ys)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

fun free :: "Expr => int list" where
"free (Var y) = Cons2 y (Nil2)"
| "free (Lam z b) = filter (% (x2 :: int) => z ~= x2) (free b)"
| "free (App c b2) = append (free c) (free b2)"

fun subst :: "int => Expr => Expr => Expr" where
"subst x y (Var y2) = (if x = y2 then y else Var y2)"
| "subst x y (Lam y3 a) =
     (if x = y3 then Lam y3 a else
        (if elem y3 (free y) then
           subst
             x y
             (Lam
                (new (append (free y) (free a)))
                (subst y3 (Var (new (append (free y) (free a)))) a))
           else
           Lam y3 (subst x y a)))"
| "subst x y (App c b2) = App (subst x y c) (subst x y b2)"

(*hipster or2 newmaximum new filter elem append free subst *)

theorem x0 :
  "!! (x :: int) (e :: Expr) (a :: Expr) (y :: int) .
     (~ (elem x (free a))) ==>
       ((elem y (free a)) = (elem y (free (subst x e a))))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
