theory lt
imports Main
        "../data/Natu"
        "../../IsaHipster"

begin

fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S x2) (S z) = lt x2 z"


end

