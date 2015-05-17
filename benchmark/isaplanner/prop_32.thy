theory prop_32
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun min2 :: "Nat => Nat => Nat" where
  "min2 (Z) y = Z"
  | "min2 (S z) (Z) = Z"
  | "min2 (S z) (S y1) = S (min2 z y1)"
  (*hipster min2 *)
  theorem x0 :
    "(min2 a b) = (min2 b a)"
    by (hipster_induct_schemes Nat.exhaust min2.simps)

end
