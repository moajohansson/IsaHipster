theory prop_81
imports Main
        "../../IsaHipster"
begin
  datatype 'a list = Nil2 | Cons2 "'a" "'a list"
  datatype Nat = Z | S "Nat"
  fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = Nil2"
  | "take (S z) (Nil2) = Nil2"
  | "take (S z) (Cons2 x2 x3) = Cons2 x2 (take z x3)"
  fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
  | "plus (S z) y = S (plus z y)"
  fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
  | "drop (S z) (Nil2) = Nil2"
  | "drop (S z) (Cons2 x2 x3) = drop z x3"
  (*hipster take plus drop *)
  theorem x0 :
    "!! (n :: Nat) (m :: Nat) (xs :: 'a list) .
       (take n (drop m xs)) = (drop m (take (plus n m) xs))"
    by (hipster_induct_schemes)
end
