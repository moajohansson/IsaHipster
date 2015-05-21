theory le
imports Main
        "../data/Nat"
        "../../IsaHipster"

begin

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"


end

