theory fac
imports Main
        "../data/Nat"
        "../funcs/mult"
        "$HIPSTER_HOME/IsaHipster"
begin

fun fac :: "Nat => Nat" where
  "fac (Z) = S Z"
| "fac (S y) = mult (S y) (fac y)"

hipster fac mult

 
end

