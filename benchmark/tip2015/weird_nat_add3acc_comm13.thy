theory weird_nat_add3acc_comm13
imports Main
        "../../IsaHipster"
begin
  datatype Nat = Z | S "Nat"
  fun add3acc :: "Nat => Nat => Nat => Nat" where
  "add3acc (Z) (Z) z = z"
  | "add3acc (Z) (S y2) z = add3acc Z y2 (S z)"
  | "add3acc (S x2) y z = add3acc x2 (S y) z"
  hipster add3acc
  theorem x0 :
    "!! (x :: Nat) (y :: Nat) (z :: Nat) .
       (add3acc x y z) = (add3acc z y x)"
    oops
end
