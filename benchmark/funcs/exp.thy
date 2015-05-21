theory exp
imports Main
        "../data/Natu"
        "../funcs/mult"
        "../../IsaHipster"
begin

fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
| "exp x (S n) = mult x (exp x n)"
 
end

