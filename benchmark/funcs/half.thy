theory half
imports Main
        "../data/Natu"
        "$HIPSTER_HOME/IsaHipster"

begin

fun half :: "Nat => Nat" where
  "half (Z) = Z"
| "half (S (Z)) = Z"
| "half (S (S z)) = S (half z)"

hipster half

end

