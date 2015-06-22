theory qfac
imports Main
        "../data/Nat"
        "../funcs/mult"
        "../../IsaHipster"
begin

fun qfac :: "Nat => Nat => Nat" where
  "qfac (Z) y = y"
| "qfac (S z) y = qfac z (mult (S z) y)"

end

