theory exp
imports Main
        "../data/Nat"
        "../funcs/mult"
        "../../IsaHipster"
begin

fun exp :: "Nat => Nat => Nat" where
  "exp x (Z) = S Z"
| "exp x (S n) = mult x (exp x n)"
 
end

