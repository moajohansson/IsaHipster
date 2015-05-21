theory lt
imports Main
        "../data/Nat"
        "../../IsaHipster"

begin

fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S x2) (S z) = lt x2 z"


end

