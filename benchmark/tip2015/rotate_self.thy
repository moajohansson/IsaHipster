theory rotate_self
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = S "Nat" | Z

datatype 'a List2 = Cons2 "'a" "'a List2" | Nil2

fun append :: "'a List2 => 'a List2 => 'a List2" where
"append (Cons2 z xs) y = Cons2 z (append xs y)"
| "append (Nil2) y = y"

fun rotate :: "Nat => 'a List2 => 'a List2" where
"rotate (S z) (Cons2 x2 x3) =
   rotate z (append x3 (Cons2 x2 (Nil2)))"
| "rotate (S z) (Nil2) = Nil2"
| "rotate (Z) y = y"

(*hipster append rotate *)

theorem x0 :
  "!! (n :: Nat) (xs :: 'a List2) .
     (rotate n (append xs xs)) = (append (rotate n xs) (rotate n xs))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
