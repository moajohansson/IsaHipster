theory fac
imports Main
        "../data/Nat"
        "../funcs/mult"
        "../../IsaHipster"
begin

fun fac :: "Nat => Nat" where
  "fac (Z) = S Z"
| "fac (S y) = mult (S y) (fac y)"
 
end

