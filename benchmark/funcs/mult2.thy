theory mult2
imports Main
        "../data/Nat"
        "../funcs/plus"
        "../../IsaHipster"
begin

fun mult2 :: "Nat => Nat => Nat" where
  "mult2 (Z) y = Z"
| "mult2 (S z) y = plus y (mult2 z y)"
 
end

