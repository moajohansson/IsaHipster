theory weird_nat_mul3acc_rrot
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun add3acc :: "Nat => Nat => Nat => Nat" where
"add3acc (Z) (Z) z = z"
| "add3acc (Z) (S y2) z = add3acc Z y2 (S z)"
| "add3acc (S x2) y z = add3acc x2 (S y) z"

fun mul3acc :: "Nat => Nat => Nat => Nat" where
"mul3acc (Z) y z = Z"
| "mul3acc (S x2) (Z) z = Z"
| "mul3acc (S x2) (S x3) (Z) = Z"
| "mul3acc (S (Z)) (S (Z)) (S (Z)) = S Z"
| "mul3acc (S (Z)) (S (Z)) (S (S x5)) =
     S (add3acc
          (mul3acc Z Z (S x5))
          (add3acc
             (mul3acc (S Z) Z (S x5)) (mul3acc Z (S Z) (S x5))
             (mul3acc Z Z (S Z)))
          (add3acc Z Z (S x5)))"
| "mul3acc (S (Z)) (S (S x6)) (S x4) =
     S (add3acc
          (mul3acc Z (S x6) x4)
          (add3acc
             (mul3acc (S Z) (S x6) x4) (mul3acc Z (S Z) x4)
             (mul3acc Z (S x6) (S Z)))
          (add3acc Z (S x6) x4))"
| "mul3acc (S (S x7)) (S x3) (S x4) =
     S (add3acc
          (mul3acc (S x7) x3 x4)
          (add3acc
             (mul3acc (S Z) x3 x4) (mul3acc (S x7) (S Z) x4)
             (mul3acc (S x7) x3 (S Z)))
          (add3acc (S x7) x3 x4))"

(*hipster add3acc mul3acc *)

theorem x0 :
  "!! (x :: Nat) (y :: Nat) (z :: Nat) .
     (mul3acc x y z) = (mul3acc z x y)"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
