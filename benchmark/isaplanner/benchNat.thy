theory benchNat
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
"plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun minus :: "Nat => Nat => Nat" where
"minus (Z) y = Z"
| "minus (S z) (Z) = S z"
| "minus (S z) (S x2) = minus z x2"

fun equal2 :: "Nat => Nat => bool" where
"equal2 (Z) (Z) = True"
| "equal2 (Z) (S z) = False"
| "equal2 (S x2) (Z) = False"
| "equal2 (S x2) (S y2) = equal2 x2 y2"

fun le :: "Nat => Nat => bool" where
"le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

fun lt :: "Nat => Nat => bool" where
"lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S x2) (S z) = lt x2 z"

fun max2 :: "Nat => Nat => Nat" where
"max2 (Z) y = y"
| "max2 (S z) (Z) = S z"
| "max2 (S z) (S x2) = S (max2 z x2)"

fun min2 :: "Nat => Nat => Nat" where
"min2 (Z) y = Z"
| "min2 (S z) (Z) = Z"
| "min2 (S z) (S y1) = S (min2 z y1)"

end

