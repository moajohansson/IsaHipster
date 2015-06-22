theory mult2
imports Main
        "../data/Natu"
        "../funcs/plus"
        "../../IsaHipster"
begin

fun mult2 :: "Nat => Nat => Nat => Nat" where
  "mult2 (Z) y z = z"
| "mult2 (S x2) y z = mult2 x2 y (plus y z)"

end

