theory double
imports Main
        "../data/Nat"
        "../../IsaHipster"
begin

fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S y) = S (S (double y))"

end

