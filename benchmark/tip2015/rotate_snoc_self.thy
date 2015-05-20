theory rotate_snoc_self
imports Main
        "../../IsaHipster"
begin

datatype 'a list = Nil2 | Cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun snoc :: "'a => 'a list => 'a list" where
"snoc x (Nil2) = Cons2 x (Nil2)"
| "snoc x (Cons2 z ys) = Cons2 z (snoc x ys)"

fun rotate :: "Nat => 'a list => 'a list" where
"rotate (Z) y = y"
| "rotate (S z) (Nil2) = Nil2"
| "rotate (S z) (Cons2 x2 x3) = rotate z (snoc x2 x3)"

fun append :: "'a list => 'a list => 'a list" where
"append (Nil2) y = y"
| "append (Cons2 z xs) y = Cons2 z (append xs y)"

(*hipster snoc rotate append *)

theorem x0 :
  "!! (n :: Nat) (xs :: 'a list) .
     (rotate n (append xs xs)) = (append (rotate n xs) (rotate n xs))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
