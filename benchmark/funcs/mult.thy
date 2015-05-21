theory mult
imports Main
        "../data/Nat"
        "../funcs/plus"
        "../../IsaHipster"
begin

fun mult :: "Nat => Nat => Nat => Nat" where
  "mult (Z) y z = z"
| "mult (S x2) y z = mult x2 y (plus y z)"

end

