theory testc
imports Main
        "../IsaHipster"
begin

datatype Nat = Z | S Nat

fun le :: "Nat => Nat => bool" where
  "le Z     y      = True"
| "le y Z      = False"
| "le (S z) (S x2) = le z x2"

fun eqN :: "Nat => Nat => bool" where
  "eqN Z      Z    = True"
| "eqN Z     (S z) = False"
| "eqN (S x)  Z    = False"
| "eqN (S x) (S y) = eqN x y"

setup{*Hip_Tac_Ops.toggle_full_types @{context}*}
setup{*Hip_Tac_Ops.set_metis_to @{context} 1000*}

hipster_cond le

end
