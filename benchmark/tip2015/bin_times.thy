theory bin_times
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  datatype Bin = One | ZeroAnd "Bin" | OneAnd "Bin"
  fun s :: "Bin => Bin" where
  "s (One) = ZeroAnd One"
  | "s (ZeroAnd xs) = OneAnd xs"
  | "s (OneAnd ys) = ZeroAnd (s ys)"
  fun plus2 :: "Bin => Bin => Bin" where
  "plus2 (One) y = s y"
  | "plus2 (ZeroAnd z) (One) = s (ZeroAnd z)"
  | "plus2 (ZeroAnd z) (ZeroAnd ys) = ZeroAnd (plus2 z ys)"
  | "plus2 (ZeroAnd z) (OneAnd xs) = OneAnd (plus2 z xs)"
  | "plus2 (OneAnd x2) (One) = s (OneAnd x2)"
  | "plus2 (OneAnd x2) (ZeroAnd zs) = OneAnd (plus2 x2 zs)"
  | "plus2 (OneAnd x2) (OneAnd ys2) = ZeroAnd (s (plus2 x2 ys2))"
  fun times :: "Bin => Bin => Bin" where
  "times (One) y = y"
  | "times (ZeroAnd xs) y = ZeroAnd (times xs y)"
  | "times (OneAnd ys) y = plus2 (ZeroAnd (times ys y)) y"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S n) y = S (plus n y)"
  fun toNat :: "Bin => Nat" where
  "toNat (One) = S Z"
  | "toNat (ZeroAnd xs) = plus (toNat xs) (toNat xs)"
  | "toNat (OneAnd ys) = S (plus (toNat ys) (toNat ys))"
  fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
  | "mult (S n) y = plus y (mult n y)"
  (*hipster s plus2 times plus toNat mult *)
  theorem x0 :
    "(toNat (times x y)) = (mult (toNat x) (toNat y))"
    by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})
end
