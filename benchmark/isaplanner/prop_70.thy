theory prop_70
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
  | "le (S z) (Z) = False"
  | "le (S z) (S x2) = le z x2"
  (*hipster le *)
  theorem x0 :
    "!! (m :: Nat) (n :: Nat) . (le m n) ==> (le m (S n))"
    by (hipster_induct_schemes)
end
