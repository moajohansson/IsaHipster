theory unequal
imports Main
        "../data/Nat"
        "../function/equal"
        "../../IsaHipster"

begin

fun unequal :: "Nat => Nat => bool" where
  "unequal x y = ~ (equal2 x y)"
 
end

