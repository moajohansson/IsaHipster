theory exp
imports Main
        "../data/Natu"
        "../funcs/mult"
        "$HIPSTER_HOME/IsaHipster"
begin

fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
| "exp x (S n) = mult x (exp x n)"

hipster exp mult plus

end

