theory mult
imports Main
        "../data/Natu"
        "../funcs/plus"
        "../../IsaHipster"
begin

fun mult :: "Nat => Nat => Nat" where
  "mult (Z) y = Z"
| "mult (S z) y = plus y (mult z y)"
 
end

