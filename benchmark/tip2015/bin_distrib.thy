theory bin_distrib
imports Main
        "../../IsaHipster"
begin

datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"

fun s :: "Bin => Bin" where
"s (One) = ZeroAnd One"
| "s (ZeroAnd xs) = OneAnd xs"
| "s (OneAnd ys) = ZeroAnd (s ys)"

fun plus :: "Bin => Bin => Bin" where
"plus (One) y = s y"
| "plus (ZeroAnd z) (One) = s (ZeroAnd z)"
| "plus (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus z ys)"
| "plus (ZeroAnd z) (OneAnd xs) = OneAnd (plus z xs)"
| "plus (OneAnd x2) (One) = s (OneAnd x2)"
| "plus (OneAnd x2) (ZeroAnd zs) = OneAnd (plus x2 zs)"
| "plus (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus x2 ys2))"

fun times :: "Bin => Bin => Bin" where
"times (One) y = y"
| "times (ZeroAnd xs) y = ZeroAnd (times xs y)"
| "times (OneAnd ys) y = plus (ZeroAnd (times ys y)) y"

hipster s plus times

theorem x0 :
  "!! (x :: Bin) (y :: Bin) (z :: Bin) .
     (times x (plus y z)) = (plus (times x y) (times x z))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
