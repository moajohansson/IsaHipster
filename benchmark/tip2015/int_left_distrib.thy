theory int_left_distrib
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Sign = Pos | Neg

datatype Nat = Zero | Succ "Nat"

datatype Z = P "Nat" | N "Nat"

fun toInteger :: "Sign => Nat => Z" where
"toInteger (Pos) y = P y"
| "toInteger (Neg) (Zero) = P Zero"
| "toInteger (Neg) (Succ m) = N m"

fun sign2 :: "Z => Sign" where
"sign2 (P y) = Pos"
| "sign2 (N z) = Neg"

fun plus2 :: "Nat => Nat => Nat" where
"plus2 (Zero) y = y"
| "plus2 (Succ n) y = Succ (plus2 n y)"

fun opposite :: "Sign => Sign" where
"opposite (Pos) = Neg"
| "opposite (Neg) = Pos"

fun timesSign :: "Sign => Sign => Sign" where
"timesSign (Pos) y = y"
| "timesSign (Neg) y = opposite y"

fun mult :: "Nat => Nat => Nat" where
"mult (Zero) y = Zero"
| "mult (Succ n) y = plus2 y (mult n y)"

fun minus :: "Nat => Nat => Z" where
"minus (Zero) (Zero) = P Zero"
| "minus (Zero) (Succ n) = N n"
| "minus (Succ m) (Zero) = P (Succ m)"
| "minus (Succ m) (Succ o) = minus m o"

fun plus :: "Z => Z => Z" where
"plus (P m) (P n) = P (plus2 m n)"
| "plus (P m) (N o) = minus m (Succ o)"
| "plus (N m2) (P n2) = minus n2 (Succ m2)"
| "plus (N m2) (N n3) = N (Succ (plus2 m2 n3))"

fun absVal :: "Z => Nat" where
"absVal (P n) = n"
| "absVal (N m) = Succ m"

fun times :: "Z => Z => Z" where
"times x y =
   toInteger
     (timesSign (sign2 x) (sign2 y)) (mult (absVal x) (absVal y))"

(*hipster toInteger
          sign2
          plus2
          opposite
          timesSign
          mult
          minus
          plus
          absVal
          times *)

theorem x0 :
  "!! (x :: Z) (y :: Z) (z :: Z) .
     (times x (plus y z)) = (plus (times x y) (times x z))"
  by (tactic {* Subgoal.FOCUS_PARAMS (K (Tactic_Data.hard_tac @{context})) @{context} 1 *})

end
