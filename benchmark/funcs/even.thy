theory even
imports Main
        "../data/Natu"
        "../../IsaHipster"

begin

fun even :: "Nat => bool" where
  "even (Z) = True"
| "even (S (Z)) = False"
| "even (S (S z)) = even z"

end

