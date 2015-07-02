theory prop_23
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun max2 :: "Nat => Nat => Nat" where
  "max2 (Z) y = y"
  | "max2 (S z) (Z) = S z"
  | "max2 (S z) (S x2) = S (max2 z x2)"
  (*hipster max2 *)
(*lemma x':"max2 (max2 x y) (S y) = max2 x (S y)"
*)
  theorem x0 :
    "(max2 a b) = (max2 b a)"
    by (hipster_induct_schemes max2.simps Nat.exhaust)
    
end
