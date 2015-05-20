theory weird_nat_mul3_assoc3
imports Main
        "../../IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun add3 :: "Nat => Nat => Nat => Nat" where
"add3 (Z) (Z) z = z"
| "add3 (Z) (S y2) z = S (add3 Z y2 z)"
| "add3 (S x2) y z = S (add3 x2 y z)"

fun mul3 :: "Nat => Nat => Nat => Nat" where
"mul3 (Z) y z = Z"
| "mul3 (S x2) (Z) z = Z"
| "mul3 (S x2) (S x3) (Z) = Z"
| "mul3 (S (Z)) (S (Z)) (S (Z)) = S Z"
| "mul3 (S (Z)) (S (Z)) (S (S x5)) =
     S (add3
          (mul3 Z Z (S x5))
          (add3 (mul3 (S Z) Z (S x5)) (mul3 Z (S Z) (S x5)) (mul3 Z Z (S Z)))
          (add3 Z Z (S x5)))"
| "mul3 (S (Z)) (S (S x6)) (S x4) =
     S (add3
          (mul3 Z (S x6) x4)
          (add3
             (mul3 (S Z) (S x6) x4) (mul3 Z (S Z) x4) (mul3 Z (S x6) (S Z)))
          (add3 Z (S x6) x4))"
| "mul3 (S (S x7)) (S x3) (S x4) =
     S (add3
          (mul3 (S x7) x3 x4)
          (add3
             (mul3 (S Z) x3 x4) (mul3 (S x7) (S Z) x4) (mul3 (S x7) x3 (S Z)))
          (add3 (S x7) x3 x4))"

(*hipster add3 mul3 *)

theorem x0 :
  "!! (x1 :: Nat) (x2 :: Nat) (x3 :: Nat) (x4 :: Nat) (x5 :: Nat) .
     (mul3 x1 (mul3 x2 x3 x4) x5) = (mul3 x1 x2 (mul3 x3 x4 x5))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
