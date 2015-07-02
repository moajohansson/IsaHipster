theory qexp
imports Main
        "../data/Nat"
        "../funcs/mult"
        "$HIPSTER_HOME/IsaHipster"
begin

fun qexp :: "Nat => Nat => Nat => Nat" where
  "qexp x (Z) z = z"
| "qexp x (S n) z = qexp x n (mult x z)"

end

