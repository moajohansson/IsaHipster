theory prop_56
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster plus drop *)
  theorem x0 :
    "!! (n :: Nat) (m :: Nat) (xs :: 'a list) .
       (drop n (drop m xs)) = (drop (plus n m) xs)"
    by (hipster_induct_schemes)
end
